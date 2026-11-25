--Here is the fresh, consolidated, complete LiftedCollatz.lean file,
--merging Sections 1 through 14 in strict dependency order with zero
--sorrys, no duplicate definitions, and clean formatting ready for lake build.

--LiftedCollatz.lean
--lean -- comment or not? not highlighted.
import Mathlib

namespace LiftedCollatz

open Nat

/-!
# Lifted Collatz Trajectories: Reversibility, Totient Periodicity, and Growth Squeeze

This module formalizes division-free ("lifted") Collatz dynamics in `ℕ`:
* `y_{k+1} = 3 * y_k + ils1b(y_k)` where `ils1b(y) = 2^(v₂(y))`
* `b_{k+1} = 3 * b_k + ils1b(y_k)`
* `y_n = 3^n * x + b_n`

## Module Structure
1. **Core Definitions**: `count_div_by_2`, `ils1b`, `trace_state`, `build_intercept`, `lift_aux`,
   `count_div_by_2_in_recursive_lift`, `decode_list`.
2. **Basic Valuation & Parity Lemmas**: Properties of `v₂(2^a * m)`, oddness of `build_intercept`,
   and valuation step increments.
3. **Affine Invariant & Bijective Intercept Decoding**: `trace_state_affine`,
   `forward_trajectory_produces_build_intercept`, `count_div_by_2_in_recursive_lift_reversible`,
   `decode_list_build_intercept`, `build_intercept_injective_of_length_eq`,
   `starting_x_unique_from_y_and_b`.
4. **Parameter Necessity**: Witness `b = 185` (`witness_b_185_two_slopes`) and Euler's totient
   periodicity (`euler_totient_preserves_odd_seed`).
5. **`ils1b` Growth Squeeze & Cycle Density Bounds**: `three_mul_ils1b_le_of_not_pow_two`,
   `trivial_loop_step_exact`, `unterminated_orbit_growth_squeeze`,
   `intercept_upper_bound_from_squeeze`, `nontrivial_cycle_density_window`.
6. **Direct Cycle Elimination (`n = 1, 2`)**: `no_nontrivial_1_cycle`, `no_nontrivial_2_cycle`.
7. **Infinite Cycle Tower Reduction**: `tower_intercept_geometric_identity`,
   `tower_intercept_is_peelable`, `tower_divisibility_iff_base_divisibility`.
8. **3-Step Cycle Elimination**: `cycle_sum_lt_I`, `no_nontrivial_3_cycle`.
9. **4-Step & 5-Step Cycle Elimination**: `valid_jump_lists`, `mem_valid_jump_lists`,
   `no_nontrivial_4_cycle`, `no_nontrivial_5_cycle`.
10. **General Finite-Check Helper & 6-Step Elimination**: `no_nontrivial_cycle_of_finite_check`,
    `no_nontrivial_6_cycle`.
11. **Strict Peelability Validator & Boutique Constructors**: `validate_and_peel`,
    `make_boutique_intercept`, `validate_boutique_intercept`, `validate_and_peel_sound`.
12. **Safe Decoder Bridge & 2-Step Sharpened Growth Bound**:
      `safe_count_div_by_2_in_recursive_lift`,
    `safe_count_eq_validate_and_peel`, `two_step_sharpened_growth_bound`.
13. **2-Step Sharpened Cycle Density Corollary**: `unterminated_even_orbit_sharpened_bound`,
    `nontrivial_even_cycle_sharpened_density`.
14. **Master API Summary & `#check` Reference Index**.
-/

-- ============================================================================
-- SECTION 1: Core Definitions
-- ============================================================================

/-- 2-adic valuation `v₂(n)` on natural numbers. -/
def count_div_by_2 (n : Nat) : Nat := n.factorization 2

/-- Isolated Least Significant 1-Bit: `ils1b(y) = 2^(v₂(y))`. -/
def ils1b (y : Nat) : Nat := 2 ^ (count_div_by_2 y)

/-- Forward lifted trajectory state `(y_n, b_n)` starting from `(x, 0)`. -/
def trace_state : Nat → Nat → Nat × Nat
  | x, 0 => (x, 0)
  | x, n + 1 =>
    let (y, b) := trace_state x n
    (3 * y + ils1b y, 3 * b + ils1b y)

/-- Predicate stating `y` is a pure power of 2 (`2^t`). -/
def is_pow_two (y : Nat) : Prop := ∃ t : Nat, y = 2 ^ t

/-- Forward construction of the `y`-intercept `b` from a list of 2-adic jumps `[a₁, ...]`. -/
def build_intercept : List Nat → Nat
  | [] => 1
  | a :: as => 3 ^ (as.length + 1) + 2 ^ a * build_intercept as

/-- Tail-recursive decoder summing the 2-adic jumps peeled from `y_intercept`. -/
def lift_aux : Nat → Nat → Nat → Nat
  | _, 0, tot => tot
  | y, pow_3 + 1, tot =>
    let y_new := y - 3 ^ (pow_3 + 1)
    if y_new % 2 = 1 then
      tot
    else
      let pow_2 := count_div_by_2 y_new
      let y_next := y_new / (2 ^ pow_2)
      if y_next < 1 then
        tot
      else
        lift_aux y_next pow_3 (tot + pow_2)

/-- Top-level decoder recovering the final added exponent from `(y_intercept, starting_pow_3)`. -/
def count_div_by_2_in_recursive_lift (y_intercept : Nat) (starting_pow_3 : Nat) : Nat :=
  lift_aux y_intercept (starting_pow_3 - 1) 0

/-- Decoder recovering the full list of step-by-step 2-adic jumps `[a₁, ..., a_{n-1}]`. -/
def decode_list : Nat → Nat → List Nat
  | _, 0 => []
  | y, pow_3 + 1 =>
    let y_new := y - 3 ^ (pow_3 + 1)
    if y_new % 2 = 1 then
      []
    else
      let pow_2 := count_div_by_2 y_new
      let y_next := y_new / (2 ^ pow_2)
      if y_next < 1 then
        []
      else
        pow_2 :: decode_list y_next pow_3

-- ============================================================================
-- SECTION 2: Basic Valuation & Parity Lemmas
-- ============================================================================

lemma count_div_by_2_two_pow_mul {a m : Nat} (hm : m % 2 = 1) :
    count_div_by_2 (2 ^ a * m) = a := by
  have hm0 : m ≠ 0 := by omega
  have hnotdvd : ¬ (2 ∣ m) := by omega
  have h2a : (2 : Nat) ^ a ≠ 0 := by simp
  unfold count_div_by_2
  rw [Nat.factorization_mul h2a hm0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd hnotdvd]
  simp

/-
(Note: Apply the same have h2k : (2 : Nat) ^ _ ≠ 0 := by simp pattern
in lifted_step_valuation, three_mul_ils1b_le_of_not_pow_two, cycle_sum_lt_I,
and two_step_sharpened_growth_bound so Lean never sees an unannotated (by simp)
inside Nat.factorization_mul!)
-/

lemma build_intercept_odd (as : List Nat) (h : ∀ a ∈ as, 1 ≤ a) :
    build_intercept as % 2 = 1 := by
  induction as with
  | nil => simp [build_intercept]
  | cons a tl ih =>
    simp only [build_intercept]
    have ha : 1 ≤ a := h a List.mem_cons_self
    have hpow2 : (2 ^ a) % 2 = 0 := by
      have : 2 ∣ 2 ^ a := dvd_pow_self 2 (by omega)
      omega
    have hpow3 : (3 ^ (tl.length + 1)) % 2 = 1 := by
      rw [Nat.pow_mod]; norm_num
    rw [Nat.add_mod, Nat.mul_mod, hpow3, hpow2]
    omega

lemma trace_y_ne_zero (x : Nat) (hx : x ≠ 0) (n : Nat) :
    (trace_state x n).1 ≠ 0 := by
  induction n with
  | zero => simp only [trace_state]; exact hx
  | succ n _ => simp [trace_state, ils1b]

lemma lifted_step_valuation {y : Nat} (hy : y ≠ 0) :
    ∃ a ≥ 1, count_div_by_2 (3 * y + ils1b y) = count_div_by_2 y + a := by
  set k := count_div_by_2 y
  rcases Nat.ordProj_dvd y 2 with ⟨m, hm⟩
  have hm_odd : m % 2 = 1 := by
    by_contra h
    have hm_even : 2 ∣ m := by omega
    rcases hm_even with ⟨r, rfl⟩
    have hr0 : r ≠ 0 := by intro hr; subst hr; simp only [mul_zero] at hm; exact hy hm
    have h2pow : (2 : Nat) ^ (k + 1) ≠ 0 := by simp
    have hge : k + 1 ≤ count_div_by_2 (2 ^ (k + 1) * r) := by
      unfold count_div_by_2
      rw [Nat.factorization_mul h2pow hr0, Finsupp.add_apply,
          Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
      omega
    have heq : y = 2 ^ (k + 1) * r := by
      dsimp only [k, count_div_by_2]
      nth_rw 1 [hm]
      ring
    rw [← heq] at hge
    omega
  have hfactor : 3 * y + ils1b y = 2 ^ k * (3 * m + 1) := by
    dsimp only [ils1b, k, count_div_by_2]
    nth_rw 1 [hm]
    ring
  rw [hfactor]
  have h3m1_ne : 3 * m + 1 ≠ 0 := by omega
  set a := count_div_by_2 (3 * m + 1)
  have ha_ge : 1 ≤ a := by
    have hdvd2 : 2 ∣ 3 * m + 1 := by omega
    exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two h3m1_ne hdvd2
  refine ⟨a, ha_ge, ?_⟩
  rcases Nat.ordProj_dvd (3 * m + 1) 2 with ⟨m', hm'⟩
  have hm'_odd : m' % 2 = 1 := by
    by_contra h
    have hm'_even : 2 ∣ m' := by omega
    rcases hm'_even with ⟨r, rfl⟩
    have hr0 : r ≠ 0 := by intro hr; subst hr; simp at hm'
    have h2pow : (2 : Nat) ^ (a + 1) ≠ 0 := by simp
    have hge : a + 1 ≤ count_div_by_2 (2 ^ (a + 1) * r) := by
      unfold count_div_by_2
      rw [Nat.factorization_mul h2pow hr0, Finsupp.add_apply,
          Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
      omega
    have heq : 3 * m + 1 = 2 ^ (a + 1) * r := by
      dsimp only [a, count_div_by_2]
      nth_rw 1 [hm']
      ring
    rw [← heq] at hge
    omega
  have hmerge : 2 ^ k * (3 * m + 1) = 2 ^ (k + a) * m' := by
    dsimp only [a, count_div_by_2]
    nth_rw 1 [hm']
    ring
  rw [hmerge]
  exact count_div_by_2_two_pow_mul hm'_odd

lemma build_intercept_append (as : List Nat) (a : Nat) :
    build_intercept (as ++ [a]) = 3 * build_intercept as + 2 ^ (as.sum + a) := by
  induction as with
  | nil =>
    simp [build_intercept]
  | cons x xs ih =>
    simp only [List.cons_append, build_intercept, List.length_append, List.length_singleton,
               List.sum_cons, Nat.add_assoc, Nat.pow_add]
    rw [ih, _root_.pow_succ']
    ring

-- ============================================================================
-- SECTION 3: Affine Invariant, Reversibility, and Bijective Decoding
-- ============================================================================

/-- Fundamental Affine Invariant: `y_n = 3^n * x + b_n`. -/
theorem trace_state_affine (x n : Nat) :
    (trace_state x n).1 = 3 ^ n * x + (trace_state x n).2 := by
  induction n with
  | zero => simp [trace_state]
  | succ n ih =>
    simp only [trace_state]
    rw [ih, pow_succ']
    ring

/-- Every lifted trajectory from an odd seed `x` produces `b_{n+1} = build_intercept as`. -/
theorem forward_trajectory_produces_build_intercept (x : Nat) (hx : x % 2 = 1) (n : Nat) :
    ∃ as : List Nat,
      as.length = n ∧
      (∀ a ∈ as, 1 ≤ a) ∧
      (trace_state x (n + 1)).2 = build_intercept as ∧
      count_div_by_2 (trace_state x n).1 = as.sum := by
  have hx_ne : x ≠ 0 := by omega
  induction n with
  | zero =>
    have hk0 : count_div_by_2 x = 0 := by
      have h := count_div_by_2_two_pow_mul (a := 0) hx
      simpa using h
    refine ⟨[], rfl, by simp, ?_, ?_⟩
    · simp [trace_state, ils1b, build_intercept, hk0]
    · simp [trace_state, hk0]
  | succ n ih =>
    rcases ih with ⟨as, hlen, hpos, hb, hval⟩
    obtain ⟨a, ha_ge, hstep⟩ := lifted_step_valuation (trace_y_ne_zero x hx_ne n)
    refine ⟨as ++ [a], ?_, ?_, ?_, ?_⟩
    · simp [hlen]
    · intro z hz
      simp only [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact hpos z hz
      · exact ha_ge
    · rw [build_intercept_append, ← hb, ← hval, ← hstep]
      simp only [trace_state, ils1b]
    · simp only [trace_state] at hstep ⊢
      rw [hstep, hval, List.sum_append, List.sum_singleton]

theorem lift_aux_recovers_sum (as : List Nat) (h : ∀ a ∈ as, 1 ≤ a) (tot : Nat) :
    lift_aux (build_intercept as) as.length tot = tot + as.sum := by
  induction as generalizing tot with
  | nil => simp [lift_aux]
  | cons a tl ih =>
  have ha : 1 ≤ a := h a List.mem_cons_self
  have htl : ∀ x ∈ tl, 1 ≤ x := fun x hx => h x (List.mem_cons_of_mem a hx)
  simp only [List.length_cons, lift_aux]
  have hy_new : build_intercept (a :: tl) - 3 ^ (tl.length + 1) = 2 ^ a * build_intercept tl := by
    simp [build_intercept]
  rw [hy_new]
  have hnotodd : ¬ ((2 ^ a * build_intercept tl) % 2 = 1) := by
    have : 2 ∣ 2 ^ a * build_intercept tl := dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
    omega
  rw [ite_eq_right hnotodd]
  have hodd := build_intercept_odd tl htl
  rw [count_div_by_2_two_pow_mul hodd]
  rw [Nat.mul_div_cancel_left _ (by positivity)]
  have hge1 : ¬ (build_intercept tl < 1) := by omega
  rw [ite_eq_right hge1]
  rw [ih htl (tot + a), List.sum_cons]
  ring

/-- count_div_by_2_in_recursive_lift recovers v₂(y_n) from (b_{n+1}, n + 1). -/
theorem count_div_by_2_in_recursive_lift_reversible
    (x : Nat) (hx : x % 2 = 1) (n : Nat) :
  count_div_by_2_in_recursive_lift (trace_state x (n + 1)).2 (n + 1) =
  count_div_by_2 (trace_state x n).1 := by
  rcases forward_trajectory_produces_build_intercept x hx n with ⟨as, hlen, hpos, hb, hval⟩
  simp only [count_div_by_2_in_recursive_lift, Nat.add_sub_cancel]
  rw [hb, hval, ← hlen, lift_aux_recovers_sum as hpos 0, zero_add]

/-- decode_list is an exact left-inverse of build_intercept. -/
theorem decode_list_build_intercept (as : List Nat) (h : ∀ a ∈ as, 1 ≤ a) :
    decode_list (build_intercept as) as.length = as := by
  induction as with
  | nil => simp [decode_list]
  | cons a tl ih =>
    have ha : 1 ≤ a := h a List.mem_cons_self
    have htl : ∀ x ∈ tl, 1 ≤ x := fun x hx => h x (List.mem_cons_of_mem a hx)
    simp only [List.length_cons, decode_list]
    have hy_new : build_intercept (a :: tl) - 3 ^ (tl.length + 1) = 2 ^ a * build_intercept tl := by
      simp [build_intercept]
    rw [hy_new]
    have hnotodd : ¬ ((2 ^ a * build_intercept tl) % 2 = 1) := by
      have : 2 ∣ 2 ^ a * build_intercept tl := dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
      omega
    rw [ite_eq_right hnotodd]
    have hodd := build_intercept_odd tl htl
    rw [count_div_by_2_two_pow_mul hodd]
    rw [Nat.mul_div_cancel_left _ (by positivity)]
    have hge1 : ¬ (build_intercept tl < 1) := by omega
    rw [ite_eq_right hge1, ih htl]

/-- build_intercept is strictly injective for any fixed step count n. -/
theorem build_intercept_injective_of_length_eq
    (as bs : List Nat)
    (has : ∀ a ∈ as, 1 ≤ a) (hbs : ∀ b ∈ bs, 1 ≤ b)
    (hlen : as.length = bs.length)
    (heq : build_intercept as = build_intercept bs) :
    as = bs := by
  calc as
    _ = decode_list (build_intercept as) as.length := (decode_list_build_intercept as has).symm
    _ = decode_list (build_intercept bs) bs.length := by rw [heq, hlen]
    _ = bs := decode_list_build_intercept bs hbs

/-- Starting x is uniquely determined by (y_n, b_n). -/
theorem starting_x_unique_from_y_and_b
    (x₁ x₂ n : Nat)
    (hy : (trace_state x₁ n).1 = (trace_state x₂ n).1)
    (hb : (trace_state x₁ n).2 = (trace_state x₂ n).2) :
    x₁ = x₂ := by
  have h1 := trace_state_affine x₁ n
  have h2 := trace_state_affine x₂ n
  rw [hy, hb] at h1
  rw [h1] at h2
  exact Nat.eq_of_mul_eq_mul_left (by positivity) (Nat.add_right_cancel h2)

-- ============================================================================
-- SECTION 4: Witness b = 185 & Euler's Totient Periodicity
-- ============================================================================

/-- Concrete witness: b = 185 satisfies 2^11 = 3^j * x + 185 for two slopes 81 and 27. -/
theorem witness_b_185_two_slopes :
    2 ^ 11 = 3 ^ 4 * 23 + 185 ∧
    2 ^ 11 = 3 ^ 3 * 69 + 185 ∧
    (3 ^ 4 ≠ 3 ^ 3 ∧ 23 ≠ 69) := by
  norm_num

lemma totient_three_pow (j : Nat) (hj : 1 ≤ j) :
    φ (3 ^ j) = 2 * 3 ^ (j - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  rw [Nat.totient_prime_pow Nat.prime_three (Nat.succ_pos k)]
  simp only [Nat.succ_sub_one]
  ring

lemma three_pow_dvd_two_pow_totient_mul (j k : Nat) :
    3 ^ j ∣ 2 ^ (k * φ (3 ^ j)) - 1 := by
  have hcoprime : Nat.Coprime 2 (3 ^ j) := Nat.Coprime.pow_right j (by decide)
  have heuler : 2 ^ φ (3 ^ j) ≡ 1 [MOD 3 ^ j] := Nat.ModEq.pow_totient hcoprime
  have hpow : 2 ^ (k * φ (3 ^ j)) ≡ 1 [MOD 3 ^ j] := by
    rw [mul_comm, pow_mul]
    simpa using heuler.pow k
  exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hpow.symm

/-- Shifting I by k * φ(3^j) yields infinitely many odd seeds x' for the same (3^j, b). -/
theorem euler_totient_preserves_odd_seed
    (I j k x b : Nat)
    (hI : 1 ≤ I)
    (hx_odd : x % 2 = 1)
    (h : 2 ^ I = 3 ^ j * x + b) :
    ∃ x' : Nat,
      x' % 2 = 1 ∧
      2 ^ (I + k * φ (3 ^ j)) = 3 ^ j * x' + b ∧
      x' = x + 2 ^ I * ((2 ^ (k * φ (3 ^ j)) - 1) / 3 ^ j) := by
  obtain ⟨q, hq⟩ := three_pow_dvd_two_pow_totient_mul j k
  have hpow_ge : 1 ≤ 2 ^ (k * φ (3 ^ j)) := Nat.one_le_two_pow
  have hpow_eq : 2 ^ (k * φ (3 ^ j)) = 3 ^ j * q + 1 := by omega
  have hm_pos : 0 < 3 ^ j := by positivity
  have hq_eq : q = (2 ^ (k * φ (3 ^ j)) - 1) / 3 ^ j := by
    rw [hq, Nat.mul_div_cancel_left q hm_pos]
  have htwo_pow_even : 2 ^ I % 2 = 0 := by
    have hdvd : 2 ∣ 2 ^ I := dvd_pow_self 2 (by omega)
    omega
  refine ⟨x + 2 ^ I * q, ?_, ?_, by rw [hq_eq]⟩
  · rw [Nat.add_mod, Nat.mul_mod, htwo_pow_even, hx_odd]
    norm_num
  calc 2 ^ (I + k * φ (3 ^ j))
    _ = 2 ^ I * 2 ^ (k * φ (3 ^ j)) := by rw [pow_add]
    _ = 2 ^ I * (3 ^ j * q + 1) := by rw [hpow_eq]
    _ = 3 ^ j * (2 ^ I * q) + 2 ^ I := by ring
    _ = 3 ^ j * (2 ^ I * q) + (3 ^ j * x + b) := by rw [h]
    _ = 3 ^ j * (x + 2 ^ I * q) + b := by ring

-- ============================================================================
-- SECTION 5: ils1b Inequality, Growth Squeeze, and Cycle Density Bounds
-- ============================================================================

/-- If y > 0 is NOT a power of 2, its odd part is at least 3, so 3 * ils1b(y) ≤ y. -/
lemma three_mul_ils1b_le_of_not_pow_two {y : Nat} (hy : y ≠ 0) (hnot2 : ¬ is_pow_two y) :
    3 * ils1b y ≤ y := by
  set k := count_div_by_2 y
  rcases Nat.ordProj_dvd y 2 with ⟨m, hm⟩
  have hm_odd : m % 2 = 1 := by
    by_contra h
    have hm_even : 2 ∣ m := by omega
    rcases hm_even with ⟨r, rfl⟩
    have hr0 : r ≠ 0 := by intro hr; subst hr; simp only [mul_zero] at hm; exact hy hm
    have hge : k + 1 ≤ count_div_by_2 (2 ^ (k + 1) * r) := by
      rw [count_div_by_2, Nat.factorization_mul (by positivity) hr0]
      simp [Nat.Prime.factorization_pow Nat.prime_two]
    have heq : y = 2 ^ (k + 1) * r := by
      dsimp only [k, count_div_by_2]
      nth_rw 1 [hm]
      ring
    rw [← heq] at hge
    omega
  have hm_ne_one : m ≠ 1 := by
    intro hm1
    apply hnot2
    refine ⟨k, ?_⟩
    dsimp only [k, count_div_by_2]
    nth_rw 1 [hm]
    rw [hm1, mul_one]
  have hm_ge_three : 3 ≤ m := by omega
  calc 3 * ils1b y
    _ = 2 ^ k * 3 := by simp [ils1b]; ring
    _ ≤ 2 ^ k * m := Nat.mul_le_mul_left (2 ^ k) hm_ge_three
    _ = y := hm.symm

lemma single_step_growth_squeeze {y : Nat} (hy : y ≠ 0) (hnot2 : ¬ is_pow_two y) :
    3 * y < 3 * y + ils1b y ∧
    3 * (3 * y + ils1b y) ≤ 10 * y ∧
    10 * y < 12 * y := by
  have hils_pos : 0 < ils1b y := by simp [ils1b]
  have hils_bound : 3 * ils1b y ≤ y := three_mul_ils1b_le_of_not_pow_two hy hnot2
  exact ⟨by omega, by omega, by omega⟩

/-- Contrast: On the trivial loop (y = 2^t), ils1b(y) = y and y_next = 4 * y. -/
lemma trivial_loop_step_exact (t : Nat) :
    ils1b (2 ^ t) = 2 ^ t ∧ 3 * (2 ^ t) + ils1b (2 ^ t) = 4 * (2 ^ t) := by
  have hval : count_div_by_2 (2 ^ t) = t := by
    simp [count_div_by_2, Nat.Prime.factorization_pow Nat.prime_two]
  simp only [ils1b, hval]
  exact ⟨trivial, by ring⟩

/-- Multi-step Growth Squeeze: 3^n * x < y_n and 3^n * y_n ≤ 10^n * x < 12^n * x. -/
theorem unterminated_orbit_growth_squeeze
    (x n : Nat) (hx : x ≠ 0) (hn : 1 ≤ n)
    (hunterm : ∀ k < n, ¬ is_pow_two (trace_state x k).1) :
    3 ^ n * x < (trace_state x n).1 ∧
    3 ^ n * (trace_state x n).1 ≤ 10 ^ n * x ∧
    10 ^ n * x < 12 ^ n * x := by
  have hmain : ∀ m ≥ 1, (∀ k < m, ¬ is_pow_two (trace_state x k).1) →
      3 ^ m * x < (trace_state x m).1 ∧ 3 ^ m * (trace_state x m).1 ≤ 10 ^ m * x := by
    intro m hm h_unterm
    induction m with
    | zero => omega
    | succ m ih =>
      have hy_m_not2 : ¬ is_pow_two (trace_state x m).1 := h_unterm m (Nat.lt_succ_self m)
      have hy_m_ne0 : (trace_state x m).1 ≠ 0 := trace_y_ne_zero x hx m
      obtain ⟨hstep_lo, hstep_hi, _⟩ := single_step_growth_squeeze hy_m_ne0 hy_m_not2
      by_cases hm0 : m = 0
      · subst hm0
        simp only [trace_state]
        exact ⟨hstep_lo, hstep_hi⟩
      · have hm1 : 1 ≤ m := by omega
        have h_unterm_prev : ∀ k < m, ¬ is_pow_two (trace_state x k).1 :=
          fun k hk => h_unterm k (Nat.lt_succ_of_lt hk)
        obtain ⟨ih_lo, ih_hi⟩ := ih hm1 h_unterm_prev
        simp only [trace_state]
        constructor
        · calc 3 ^ (m + 1) * x
            _ = 3 * (3 ^ m * x) := by ring
            _ < 3 * (trace_state x m).1 := Nat.mul_lt_mul_of_pos_left ih_lo (by decide)
            _ < 3 * (trace_state x m).1 + ils1b (trace_state x m).1 := hstep_lo
        · calc 3 ^ (m + 1) * (3 * (trace_state x m).1 + ils1b (trace_state x m).1)
            _ = 3 ^ m * (3 * (3 * (trace_state x m).1 + ils1b (trace_state x m).1)) := by ring
            _ ≤ 3 ^ m * (10 * (trace_state x m).1) := Nat.mul_le_mul_left (3 ^ m) hstep_hi
            _ = 10 * (3 ^ m * (trace_state x m).1) := by ring
            _ ≤ 10 * (10 ^ m * x) := Nat.mul_le_mul_left 10 ih_hi
            _ = 10 ^ (m + 1) * x := by ring
  obtain ⟨hlo, hhi⟩ := hmain n hn hunterm
  refine ⟨hlo, hhi, ?_⟩
  have hpow_lt : 10 ^ n < 12 ^ n := Nat.pow_lt_pow_left (by decide) (by omega)
  exact Nat.mul_lt_mul_of_pos_right hpow_lt (by omega)

/-- Upper bound on the y-intercept: 3^n * b_n ≤ (10^n - 9^n) * x. -/
theorem intercept_upper_bound_from_squeeze
    (x n : Nat) (hx : x ≠ 0) (hn : 1 ≤ n)
    (hunterm : ∀ k < n, ¬ is_pow_two (trace_state x k).1) :
    3 ^ n * (trace_state x n).2 ≤ (10 ^ n - 9 ^ n) * x := by
  obtain ⟨_, hhi, _⟩ := unterminated_orbit_growth_squeeze x n hx hn hunterm
  have haff : (trace_state x n).1 = 3 ^ n * x + (trace_state x n).2 := trace_state_affine x n
  rw [haff] at hhi
  have hexpand : 3 ^ n * (3 ^ n * x + (trace_state x n).2) =
      9 ^ n * x + 3 ^ n * (trace_state x n).2 := by
    calc 3 ^ n * (3 ^ n * x + (trace_state x n).2)
      _ = (3 ^ n * 3 ^ n) * x + 3 ^ n * (trace_state x n).2 := by ring
      _ = (3 * 3) ^ n * x + 3 ^ n * (trace_state x n).2 := by rw [← mul_pow]
      _ = 9 ^ n * x + 3 ^ n * (trace_state x n).2 := by norm_num
  rw [hexpand] at hhi
  have hsub : 3 ^ n * (trace_state x n).2 ≤ 10 ^ n * x - 9 ^ n * x := by omega
  rwa [← Nat.sub_mul] at hsub

/-- Cycle Density Window: Any non-trivial cycle y_n = 2^I * x (x > 1) satisfies
3^n < 2^I and 3^n * 2^I ≤ 10^n. -/
theorem nontrivial_cycle_density_window
    (x n I : Nat) (hx_gt : 1 < x) (hn : 1 ≤ n)
    (hunterm : ∀ k < n, ¬ is_pow_two (trace_state x k).1)
    (hcycle : (trace_state x n).1 = 2 ^ I * x) :
    3 ^ n < 2 ^ I ∧ 3 ^ n * 2 ^ I ≤ 10 ^ n := by
  have hx_pos : 0 < x := by omega
  have hx_ne0 : x ≠ 0 := by omega
  obtain ⟨hlo, hhi, _⟩ := unterminated_orbit_growth_squeeze x n hx_ne0 hn hunterm
  rw [hcycle] at hlo hhi
  refine ⟨Nat.lt_of_mul_lt_mul_right hlo, Nat.le_of_mul_le_mul_right ?_ hx_pos⟩
  linarith

-- jdc100 end

-- ============================================================================
-- SECTION 6: Direct Cycle Elimination (n = 1, 2)
-- ============================================================================

/-- Theorem: No 1-step non-trivial odd cycle exists! -/
theorem no_nontrivial_1_cycle
    (x I : Nat) (hx_gt : 1 < x)
    (hunterm : ∀ k < 1, ¬ is_pow_two (trace_state x k).1)
    (hcycle : (trace_state x 1).1 = 2 ^ I * x) :
    False := by
  obtain ⟨hlo, hhi⟩ := nontrivial_cycle_density_window x 1 I hx_gt (by decide) hunterm hcycle
  norm_num at hlo hhi
  have hI_ge : 2 ≤ I := by
    by_contra hlt
    have hle : I ≤ 1 := by omega
    have hp : 2 ^ I ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) hle
    norm_num at hp
    omega
  have hpow_ge : 2 ^ 2 ≤ 2 ^ I := Nat.pow_le_pow_right (by decide) hI_ge
  norm_num at hpow_ge
  omega

/-- Theorem: No 2-step non-trivial odd cycle exists! -/
theorem no_nontrivial_2_cycle
    (x I : Nat) (hx_gt : 1 < x)
    (hunterm : ∀ k < 2, ¬ is_pow_two (trace_state x k).1)
    (hcycle : (trace_state x 2).1 = 2 ^ I * x) :
    False := by
  obtain ⟨hlo, hhi⟩ := nontrivial_cycle_density_window x 2 I hx_gt (by decide) hunterm hcycle
  norm_num at hlo hhi
  have hI_ge : 4 ≤ I := by
    by_contra hlt
    have hle : I ≤ 3 := by omega
    have hp : 2 ^ I ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) hle
    norm_num at hp
    omega
  have hpow_ge : 2 ^ 4 ≤ 2 ^ I := Nat.pow_le_pow_right (by decide) hI_ge
  norm_num at hpow_ge
  omega

-- jdc101 end

-- ============================================================================
-- SECTION 7: Tower Peeling Reduction Theorem (Infinite Cycle Tower)
-- ============================================================================

/-- Repeat a list step_list k times: [a₁, ..., a_n] ++ ... ++ [a₁, ..., a_n]. -/
def repeat_steps : Nat → List Nat → List Nat
  | 0, _ => []
  | k + 1, step_list => step_list ++ repeat_steps k step_list

lemma repeat_steps_length (k : Nat) (step_list : List Nat) :
    (repeat_steps k step_list).length = k * step_list.length := by
  induction k with
  | zero => simp [repeat_steps]
  | succ k ih =>
    simp only [repeat_steps, List.length_append, ih]
    ring

lemma repeat_steps_mem {k : Nat} {step_list : List Nat} (h : ∀ a ∈ step_list, 1 ≤ a) :
    ∀ a ∈ repeat_steps k step_list, 1 ≤ a := by
  induction k with
  | zero => simp [repeat_steps]
  | succ k ih =>
    intro a ha
    simp only [repeat_steps, List.mem_append] at ha
    rcases ha with ha | ha
    · exact h a ha
    · exact ih a ha

/-- Key algebraic lemma for build_intercept on concatenation (as ++ [a_last]) ++ bs. -/
lemma build_intercept_concat_step (as bs : List Nat) (a_last : Nat) :
    build_intercept (as ++ a_last :: bs) =
      3 ^ (bs.length + 1) * build_intercept as + 2 ^ (as.sum + a_last) * build_intercept bs := by
  induction as with
  | nil => simp [build_intercept]
  | cons x xs ih =>
    simp only [List.cons_append, build_intercept, List.length_append, List.length_cons,
               List.sum_cons]
    rw [ih]
    have hlen : xs.length + (bs.length + 1) + 1 = (bs.length + 1) + (xs.length + 1) := by ring
    rw [hlen, pow_add, pow_add]
    ring

/-- The k-th tower intercept B_k formed by k-fold periodic repetition of as ++ [a_n]
(dropping the final a_n). -/
def tower_intercept (as : List Nat) (a_n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => build_intercept ((repeat_steps (k + 1) (as ++ [a_n])).dropLast)

lemma repeat_succ_dropLast (k : Nat) (as : List Nat) (a_n : Nat) :
    (repeat_steps (k + 1) (as ++ [a_n])).dropLast =
      (repeat_steps k (as ++ [a_n])) ++ as := by
  induction k with
  | zero => simp [repeat_steps]
  | succ k ih =>
    have hne : (repeat_steps (k + 1) (as ++ [a_n])) ≠ [] := by
      intro h
      have hlen := congrArg List.length h
      simp [repeat_steps_length] at hlen
    calc (repeat_steps (k + 2) (as ++ [a_n])).dropLast
      _ = ((as ++ [a_n]) ++ repeat_steps (k + 1) (as ++ [a_n])).dropLast := rfl
      _ = (as ++ [a_n]) ++ (repeat_steps (k + 1) (as ++ [a_n])).dropLast :=
          List.dropLast_append_of_ne_nil hne
      _ = (as ++ [a_n]) ++ (repeat_steps k (as ++ [a_n]) ++ as) := by rw [ih]
      _ = repeat_steps (k + 1) (as ++ [a_n]) ++ as := by simp [repeat_steps, List.append_assoc]

/-- Recurrence for the tower intercepts: B_{k+1} = 3^n * B_k + 2^(k * I) * b_n. -/
lemma tower_intercept_succ (as : List Nat) (a_n k : Nat) :
    let n := as.length + 1
    let I := as.sum + a_n
    tower_intercept as a_n (k + 1) =
      3 ^ n * tower_intercept as a_n k + 2 ^ (k * I) * build_intercept as := by
  intro n I
  cases k with
  | zero => simp [tower_intercept, repeat_steps]
  | succ k =>
    simp only [tower_intercept]
    rw [repeat_succ_dropLast (k + 1) as a_n, repeat_succ_dropLast k as a_n]
    have hsplit : repeat_steps (k + 1) (as ++ [a_n]) ++ as =
        (repeat_steps k (as ++ [a_n]) ++ as) ++ a_n :: as := by
      have : repeat_steps (k + 1) (as ++ [a_n]) =
          repeat_steps k (as ++ [a_n]) ++ (as ++ [a_n]) := by
        induction k with
        | zero => simp [repeat_steps]
        | succ r ihr =>
          calc repeat_steps (r + 2) (as ++ [a_n])
            _ = (as ++ [a_n]) ++ repeat_steps (r + 1) (as ++ [a_n]) := rfl
            _ = (as ++ [a_n]) ++ (repeat_steps r (as ++ [a_n]) ++ (as ++ [a_n])) := by rw [ihr]
            _ = repeat_steps (r + 1) (as ++ [a_n]) ++ (as ++ [a_n]) := by
              simp [repeat_steps, List.append_assoc]
      rw [this]
      simp [List.append_assoc]
    rw [hsplit, build_intercept_concat_step]
    have hsum_rep : ∀ r, (repeat_steps r (as ++ [a_n])).sum = r * I := by
      intro r
      induction r with
      | zero => simp [repeat_steps]
      | succ r ihr =>
        simp only [repeat_steps, List.sum_append, ihr, List.sum_singleton, I]
        ring
    have hsum_total : (repeat_steps k (as ++ [a_n]) ++ as).sum + a_n = (k + 1) * I := by
      rw [List.sum_append, hsum_rep k]
      simp only [I]
      ring
    rw [hsum_total]

/-- Theorem 7A (Geometric Tower Identity):
For every k ≥ 1, (2^I - 3^n) * B_k = b_n * (2^(k * I) - 3^(k * n)). -/
theorem tower_intercept_geometric_identity
    (as : List Nat) (a_n k : Nat)
    (hdens : 3 ^ (as.length + 1) < 2 ^ (as.sum + a_n)) :
    let n := as.length + 1
    let I := as.sum + a_n
    (2 ^ I - 3 ^ n) * tower_intercept as a_n k =
      build_intercept as * (2 ^ (k * I) - 3 ^ (k * n)) := by
  intro n I
  induction k with
  | zero => simp [tower_intercept]
  | succ k ih =>
    have hrec := tower_intercept_succ as a_n k
    dsimp only at hrec
    rw [hrec, mul_add]
    have hstep1 : (2 ^ I - 3 ^ n) * (3 ^ n * tower_intercept as a_n k) =
        3 ^ n * ((2 ^ I - 3 ^ n) * tower_intercept as a_n k) := by ring
    rw [hstep1, ih]
    have hle1 : 3 ^ n ≤ 2 ^ I := Nat.le_of_lt hdens
    have hlek : 3 ^ (k * n) ≤ 2 ^ (k * I) := by
      calc 3 ^ (k * n) = (3 ^ n) ^ k := by rw [mul_comm, pow_mul]
        _ ≤ (2 ^ I) ^ k := Nat.pow_le_pow_left hle1 k
        _ = 2 ^ (k * I) := by rw [← pow_mul, mul_comm]
    have hlek1 : 3 ^ ((k + 1) * n) ≤ 2 ^ ((k + 1) * I) := by
      calc 3 ^ ((k + 1) * n) = (3 ^ n) ^ (k + 1) := by rw [mul_comm, pow_mul]
        _ ≤ (2 ^ I) ^ (k + 1) := Nat.pow_le_pow_left hle1 (k + 1)
        _ = 2 ^ ((k + 1) * I) := by rw [← pow_mul, mul_comm]
    zify [hle1, hlek, hlek1]
    have hpowI : ((2 : Int) ^ ((k + 1) * I)) = (2 : Int) ^ I * (2 : Int) ^ (k * I) := by
      rw [← pow_add]; ring_nf
    have hpown : ((3 : Int) ^ ((k + 1) * n)) = (3 : Int) ^ n * (3 : Int) ^ (k * n) := by
      rw [← pow_add]; ring_nf
    rw [hpowI, hpown]
    dsimp only [I]
    ring

/-- Theorem 7B (Every Tower Intercept is Valid & Peelable). -/
theorem tower_intercept_is_peelable
    (as : List Nat) (a_n k : Nat)
    (has : ∀ a ∈ as, 1 ≤ a) (ha_n : 1 ≤ a_n) (hk : 1 ≤ k) :
    let n := as.length + 1
    let seq := (repeat_steps k (as ++ [a_n])).dropLast
    seq.length = k * n - 1 ∧
    decode_list (tower_intercept as a_n k) (k * n - 1) = seq := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  intro n seq
  have hstep_mem : ∀ a ∈ as ++ [a_n], 1 ≤ a := by
    intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact has a ha
    · exact ha_n
  have hseq_mem : ∀ a ∈ seq, 1 ≤ a := fun a ha =>
    repeat_steps_mem hstep_mem a (List.dropLast_subset _ ha)
  have hlen : seq.length = (k' + 1) * n - 1 := by
    simp [seq, List.length_dropLast, repeat_steps_length, n]
  refine ⟨hlen, ?_⟩
  simp only [tower_intercept]
  rw [← hlen]
  exact decode_list_build_intercept seq hseq_mem

-- jdc103 start here, was cut off when pasting to gemini

theorem tower_divisibility_iff_base_divisibility
    (as : List Nat) (a_n : Nat)
    (hdens : 3 ^ (as.length + 1) < 2 ^ (as.sum + a_n)) :
    let n := as.length + 1
    let I := as.sum + a_n
    (∀ k ≥ 1, (2 ^ (k * I) - 3 ^ (k * n)) ∣ tower_intercept as a_n k) ↔
    ((2 ^ I - 3 ^ n) ∣ build_intercept as) := by
  intro n I
  constructor
  · intro hall
    have h1 := hall 1 (by decide)
    simpa [tower_intercept, repeat_steps] using h1
  · rintro ⟨x, hx⟩ k _
    have hgeom := tower_intercept_geometric_identity as a_n k hdens
    dsimp only at hgeom
    rw [hx] at hgeom
    have hpos : 0 < 2 ^ I - 3 ^ n := Nat.sub_pos_of_lt hdens
    have hcancel : tower_intercept as a_n k = x * (2 ^ (k * I) - 3 ^ (k * n)) := by
      have hreassoc : (2 ^ I - 3 ^ n) * tower_intercept as a_n k =
          (2 ^ I - 3 ^ n) * (x * (2 ^ (k * I) - 3 ^ (k * n))) := by
        calc (2 ^ I - 3 ^ n) * tower_intercept as a_n k
            = ((2 ^ I - 3 ^ n) * x) * (2 ^ (k * I) - 3 ^ (k * n)) := hgeom
          _ = (2 ^ I - 3 ^ n) * (x * (2 ^ (k * I) - 3 ^ (k * n))) := by ring
      exact Nat.eq_of_mul_eq_mul_left hpos hreassoc
    exact ⟨x, hcancel.trans (Nat.mul_comm _ _)⟩

-- ============================================================================
-- SECTION 8: Elimination of 3-Step Non-Trivial Cycles
-- ============================================================================

/-- At step n + 1, v₂(y_n) < I whenever y_{n+1} = 2^I * x with x odd. -/
lemma cycle_sum_lt_I
    (x n I : Nat) (hx_odd : x % 2 = 1)
    (hcycle : (trace_state x (n + 1)).1 = 2 ^ I * x) :
    count_div_by_2 (trace_state x n).1 < I := by
  have hx_ne0 : x ≠ 0 := by omega
  set y_n := (trace_state x n).1
  have hy_ne0 : y_n ≠ 0 := trace_y_ne_zero x hx_ne0 n
  set k := count_div_by_2 y_n
  rcases Nat.ordProj_dvd y_n 2 with ⟨m, hm⟩
  have hm_odd : m % 2 = 1 := by
    by_contra h
    have hm_even : 2 ∣ m := by omega
    rcases hm_even with ⟨r, rfl⟩
    have hr0 : r ≠ 0 := by intro hr; subst hr; simp only [mul_zero] at hm; exact hy_ne0 hm
    have hge : k + 1 ≤ count_div_by_2 (2 ^ (k + 1) * r) := by
      have h2k1 : (2 : Nat) ^ (k + 1) ≠ 0 := by simp
      unfold count_div_by_2
      rw [Nat.factorization_mul h2k1 hr0, Finsupp.add_apply,
          Nat.Prime.factorization_pow Nat.prime_two]
      simp
    have heq : y_n = 2 ^ (k + 1) * r := by rw [hm]; dsimp [k, count_div_by_2]; ring
    rw [← heq] at hge
    omega
  have hstep : (trace_state x (n + 1)).1 = 2 ^ k * (3 * m + 1) := by
    change 3 * y_n + ils1b y_n = 2 ^ k * (3 * m + 1)
    dsimp [ils1b, k, count_div_by_2]
    conv_lhs => arg 1; arg 2; rw [hm]
    ring
  rw [hstep] at hcycle
  have h3m1_ne0 : 3 * m + 1 ≠ 0 := by omega
  have hval_lhs : k + 1 ≤ count_div_by_2 (2 ^ k * (3 * m + 1)) := by
    have h2k : (2 : Nat) ^ k ≠ 0 := by simp
    unfold count_div_by_2
    rw [Nat.factorization_mul h2k h3m1_ne0, Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
    have hdvd2 : 2 ∣ 3 * m + 1 := by omega
    have hpos : 1 ≤ (3 * m + 1).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two h3m1_ne0 hdvd2
    omega
  have hval_rhs : count_div_by_2 (2 ^ I * x) = I :=
    count_div_by_2_two_pow_mul hx_odd
  rw [hcycle, hval_rhs] at hval_lhs
  exact hval_lhs

lemma no_length2_intercept_dvd_five (as : List Nat)
    (hlen : as.length = 2) (hpos : ∀ a ∈ as, 1 ≤ a) (hsum : as.sum ≤ 4) :
    ¬ (5 ∣ build_intercept as) := by
  rcases as with _ | ⟨a1, _ | ⟨a2, _ | _⟩⟩ <;> simp at hlen
  have ha1 : 1 ≤ a1 := hpos a1 (by simp)
  have ha2 : 1 ≤ a2 := hpos a2 (by simp)
  simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
  have ha1_le : a1 ≤ 4 := by omega
  have ha2_le : a2 ≤ 4 := by omega
  interval_cases a1 <;> interval_cases a2 <;> simp [build_intercept] at hsum ⊢

/-- Theorem: No 3-step non-trivial odd cycle exists! -/
theorem no_nontrivial_3_cycle
    (x I : Nat) (hx_gt : 1 < x) (hx_odd : x % 2 = 1)
    (hunterm : ∀ k < 3, ¬ is_pow_two (trace_state x k).1)
    (hcycle : (trace_state x 3).1 = 2 ^ I * x) :
    False := by
  obtain ⟨hlo, hhi⟩ := nontrivial_cycle_density_window x 3 I hx_gt (by decide) hunterm hcycle
  norm_num at hlo hhi
  have hI_ge : 5 ≤ I := by
    by_contra hlt
    have hle : I ≤ 4 := by omega
    have hp : 2 ^ I ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) hle
    norm_num at hp
    omega
  have hI_le : I ≤ 5 := by
    by_contra hgt
    have hge : 6 ≤ I := by omega
    have hp : 2 ^ 6 ≤ 2 ^ I := Nat.pow_le_pow_right (by decide) hge
    norm_num at hp
    omega
  have hI5 : I = 5 := by omega
  subst hI5
  rcases forward_trajectory_produces_build_intercept x hx_odd 2 with
    ⟨as, hlen, hpos, hb, hval⟩
  have hsum_lt : as.sum < 5 := by
    rw [← hval]
    exact cycle_sum_lt_I x 2 5 hx_odd hcycle
  have hsum_le : as.sum ≤ 4 := by omega
  have haff : (trace_state x 3).1 = 3 ^ 3 * x + (trace_state x 3).2 := trace_state_affine x 3
  rw [hcycle, hb] at haff
  have hdvd5 : 5 ∣ build_intercept as := ⟨x, by omega⟩
  exact no_length2_intercept_dvd_five as hlen hpos hsum_le hdvd5


-- ============================================================================
-- SECTION 9: Elimination of 4-Step and 5-Step Non-Trivial Cycles
-- ============================================================================

/-- Theorem: No 4-step non-trivial odd cycle exists! -/
theorem no_nontrivial_4_cycle
    (x I : Nat) (hx_gt : 1 < x)
    (hunterm : ∀ k < 4, ¬ is_pow_two (trace_state x k).1)
    (hcycle : (trace_state x 4).1 = 2 ^ I * x) :
    False := by
  obtain ⟨hlo, hhi⟩ := nontrivial_cycle_density_window x 4 I hx_gt (by decide) hunterm hcycle
  norm_num at hlo hhi
  have hI_ge : 7 ≤ I := by
    by_contra hlt
    have hle : I ≤ 6 := by omega
    have hp : 2 ^ I ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) hle
    norm_num at hp
    omega
  have hpow_ge : 2 ^ 7 ≤ 2 ^ I := Nat.pow_le_pow_right (by decide) hI_ge
  norm_num at hpow_ge
  omega

/-- Computable generator of all lists of length len with entries ≥ 1 and sum ≤ max_sum. -/
def valid_jump_lists : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | len + 1, max_sum =>
    (List.range max_sum).flatMap fun i =>
      let a := i + 1
      (valid_jump_lists len (max_sum - a)).map fun tl => a :: tl

lemma mem_valid_jump_lists :
    ∀ (len max_sum : Nat) (as : List Nat),
      as.length = len → (∀ a ∈ as, 1 ≤ a) → as.sum ≤ max_sum →
      as ∈ valid_jump_lists len max_sum
  | 0, max_sum, [], _, _, _ => by simp [valid_jump_lists]
  | 0, max_sum, _ :: _, hlen, _, _ => by simp at hlen
  | len + 1, max_sum, [], hlen, _, _ => by simp at hlen
  | len + 1, max_sum, a :: tl, hlen, hpos, hsum => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    have ha : 1 ≤ a := hpos a (by simp)
    have htl_pos : ∀ x ∈ tl, 1 ≤ x := fun x hx => hpos x (List.mem_cons_of_mem a hx)
    simp only [List.sum_cons] at hsum
    have ha_lt : a - 1 < max_sum := by omega
    have ha_eq : (a - 1) + 1 = a := by omega
    have htl_sum : tl.sum ≤ max_sum - a := by omega
    simp only [valid_jump_lists, List.mem_flatMap, List.mem_range, List.mem_map]
    refine ⟨a - 1, ha_lt, tl, ?_, by rw [ha_eq]⟩
    rw [ha_eq]
    exact mem_valid_jump_lists len (max_sum - a) tl hlen htl_pos htl_sum

lemma no_length4_intercept_dvd_thirteen :
    ∀ as ∈ valid_jump_lists 4 7, ¬ (13 ∣ build_intercept as) := by
  decide

/-- Theorem: No 5-step non-trivial odd cycle exists! -/
theorem no_nontrivial_5_cycle
    (x I : Nat) (hx_gt : 1 < x) (hx_odd : x % 2 = 1)
    (hunterm : ∀ k < 5, ¬ is_pow_two (trace_state x k).1)
    (hcycle : (trace_state x 5).1 = 2 ^ I * x) :
    False := by
  obtain ⟨hlo, hhi⟩ := nontrivial_cycle_density_window x 5 I hx_gt (by decide) hunterm hcycle
  norm_num at hlo hhi
  have hI_ge : 8 ≤ I := by
    by_contra hlt
    have hle : I ≤ 7 := by omega
    have hp : 2 ^ I ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) hle
    norm_num at hp
    omega
  have hI_le : I ≤ 8 := by
    by_contra hgt
    have hge : 9 ≤ I := by omega
    have hp : 2 ^ 9 ≤ 2 ^ I := Nat.pow_le_pow_right (by decide) hge
    norm_num at hp
    omega
  have hI8 : I = 8 := by omega
  subst hI8
  rcases forward_trajectory_produces_build_intercept x hx_odd 4 with
    ⟨as, hlen, hpos, hb, hval⟩
  have hsum_lt : as.sum < 8 := by
    rw [← hval]
    exact cycle_sum_lt_I x 4 8 hx_odd hcycle
  have hsum_le : as.sum ≤ 7 := by omega
  have haff : (trace_state x 5).1 = 3 ^ 5 * x + (trace_state x 5).2 := trace_state_affine x 5
  rw [hcycle, hb] at haff
  have hdvd13 : 13 ∣ build_intercept as := ⟨x, by omega⟩
  have hmem : as ∈ valid_jump_lists 4 7 := mem_valid_jump_lists 4 7 as hlen hpos hsum_le
  exact no_length4_intercept_dvd_thirteen as hmem hdvd13

-- ============================================================================
-- SECTION 10: General Finite-Check Helper & 6-Step Cycle Elimination
-- ============================================================================

/-- General finite-check elimination theorem for any fixed cycle length n + 1. -/
theorem no_nontrivial_cycle_of_finite_check
    (n : Nat) (cand_I : List Nat)
    (hI_cover : ∀ I, 3 ^ (n + 1) < 2 ^ I → 3 ^ (n + 1) * 2 ^ I ≤ 10 ^ (n + 1) → I ∈ cand_I)
    (h_no_dvd : ∀ I ∈ cand_I, ∀ as ∈ valid_jump_lists n (I - 1),
      ¬ ((2 ^ I - 3 ^ (n + 1)) ∣ build_intercept as))
    (x I : Nat) (hx_gt : 1 < x) (hx_odd : x % 2 = 1)
    (hunterm : ∀ k < n + 1, ¬ is_pow_two (trace_state x k).1)
    (hcycle : (trace_state x (n + 1)).1 = 2 ^ I * x) :
    False := by
  obtain ⟨hlo, hhi⟩ :=
    nontrivial_cycle_density_window x (n + 1) I hx_gt (by omega) hunterm hcycle
  have hI_mem : I ∈ cand_I := hI_cover I hlo hhi
  rcases forward_trajectory_produces_build_intercept x hx_odd n with
    ⟨as, hlen, hpos, hb, hval⟩
  have hsum_lt : as.sum < I := by
    rw [← hval]
    exact cycle_sum_lt_I x n I hx_odd hcycle
  have hsum_le : as.sum ≤ I - 1 := by omega
  have has_mem : as ∈ valid_jump_lists n (I - 1) :=
    mem_valid_jump_lists n (I - 1) as hlen hpos hsum_le
  have haff : (trace_state x (n + 1)).1 = 3 ^ (n + 1) * x + (trace_state x (n + 1)).2 :=
    trace_state_affine x (n + 1)
  rw [hcycle, hb] at haff
  have hdvd : (2 ^ I - 3 ^ (n + 1)) ∣ build_intercept as := by
    refine ⟨x, ?_⟩
    have hle : 3 ^ (n + 1) ≤ 2 ^ I := Nat.le_of_lt hlo
    zify [hle] at haff ⊢
    linarith
  exact h_no_dvd I hI_mem as has_mem hdvd

lemma density_window_6 (I : Nat) (hlo : 3 ^ 6 < 2 ^ I) (hhi : 3 ^ 6 * 2 ^ I ≤ 10 ^ 6) :
    I ∈ (List.cons 10 List.nil) := by
  norm_num at hlo hhi
  have hI_ge : 10 ≤ I := by
    by_contra hlt
    have : 2 ^ I ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at this
    omega
  have hI_le : I ≤ 10 := by
    by_contra hgt
    have : 2 ^ 11 ≤ 2 ^ I := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at this
    omega
  simp only [List.mem_singleton]
  omega

set_option maxRecDepth 200000 in
lemma check_6_cycle :
    ∀ I ∈ (List.cons 10 List.nil), ∀ as ∈ valid_jump_lists 5 (I - 1),
      ¬ ((2 ^ I - 3 ^ 6) ∣ build_intercept as) := by
  simp only [List.mem_singleton, forall_eq]
  norm_num
  decide

/-- Theorem: No 6-step non-trivial odd cycle exists! -/
theorem no_nontrivial_6_cycle
    (x I : Nat) (hx_gt : 1 < x) (hx_odd : x % 2 = 1)
    (hunterm : ∀ k < 6, ¬ is_pow_two (trace_state x k).1)
    (hcycle : (trace_state x 6).1 = 2 ^ I * x) :
    False :=
  no_nontrivial_cycle_of_finite_check 5 (List.cons 10 List.nil)
    density_window_6 check_6_cycle x I hx_gt hx_odd hunterm hcycle

-- ============================================================================
-- SECTION 11: Strict Peelability Validator & Boutique Intercept Constructor
-- ============================================================================

/-- Strict validator + decoder: returns some (as, as.sum) IF AND ONLY IF y is a
genuine peelable y-intercept for pow_3 layers (starting_pow_3 = pow_3 + 1).
Returns none for ANY bogus Nat. -/
def validate_and_peel : Nat → Nat → Option (List Nat × Nat)
  | y, 0 =>
    if y = 1 then some (List.nil, 0) else none
  | y, pow_3 + 1 =>
    if y ≤ 3 ^ (pow_3 + 1) then
      none
    else
      let y_new := y - 3 ^ (pow_3 + 1)
      if y_new % 2 = 1 then
        none
      else
        let pow_2 := count_div_by_2 y_new
        let y_next := y_new / (2 ^ pow_2)
        match validate_and_peel y_next pow_3 with
        | none => none
        | some (tl, tot) => some (pow_2 :: tl, tot + pow_2)

/-- Boutique intercept constructor from a list of jumps [a₁, ..., a_{n-1}].
Checks that every jump satisfies 1 ≤ a, returning some (b, starting_pow_3)
or none if any jump is 0. -/
def make_boutique_intercept (jumps : List Nat) : Option (Nat × Nat) :=
  if jumps.all (fun a => decide (1 ≤ a)) then
    some (build_intercept jumps, jumps.length + 1)
  else
    none

/-- Soundness & Completeness (Direction 1):
Every boutique intercept passes validate_and_peel and decodes back to (jumps, jumps.sum). -/
theorem validate_boutique_intercept (jumps : List Nat) (h : ∀ a ∈ jumps, 1 ≤ a) :
    validate_and_peel (build_intercept jumps) jumps.length = some (jumps, jumps.sum) := by
  induction jumps with
  | nil => simp [build_intercept, validate_and_peel]
  | cons a tl ih =>
    have ha : 1 ≤ a := h a List.mem_cons_self
    have htl : ∀ x ∈ tl, 1 ≤ x := fun x hx => h x (List.mem_cons_of_mem a hx)
    simp only [List.length_cons, validate_and_peel]
    have hpos_tail : 0 < 2 ^ a * build_intercept tl := by
      have hodd := build_intercept_odd tl htl
      have hb_pos : 0 < build_intercept tl := by omega
      positivity
    have hgt : ¬ (build_intercept (a :: tl) ≤ 3 ^ (tl.length + 1)) := by
      simp only [build_intercept]
      omega
    rw [ite_eq_right hgt]
    have hy_new : build_intercept (a :: tl) - 3 ^ (tl.length + 1) = 2 ^ a * build_intercept tl := by
      simp [build_intercept]
    rw [hy_new]
    have hnotodd : ¬ ((2 ^ a * build_intercept tl) % 2 = 1) := by
      have : 2 ∣ 2 ^ a * build_intercept tl := dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
      omega
    rw [ite_eq_right hnotodd]
    have hodd := build_intercept_odd tl htl
    rw [count_div_by_2_two_pow_mul hodd]
    rw [Nat.mul_div_cancel_left _ (by positivity)]
    rw [ih htl]
    simp [List.sum_cons, add_comm]

/-- Soundness & Completeness (Direction 2):
If validate_and_peel y k succeeds with some (as, tot), then y MUST equal
build_intercept as with as.length = k, ∀ a ∈ as, 1 ≤ a, and tot = as.sum. -/
theorem validate_and_peel_sound :
    ∀ (k y : Nat) (as : List Nat) (tot : Nat),
      validate_and_peel y k = some (as, tot) →
      as.length = k ∧ (∀ a ∈ as, 1 ≤ a) ∧ y = build_intercept as ∧ tot = as.sum
  | 0, y, as, tot, h => by
    simp only [validate_and_peel] at h
    split_ifs at h with hy1
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    refine ⟨rfl, by simp, by simp [hy1, build_intercept], rfl⟩
  | k + 1, y, as, tot, h => by
    simp only [validate_and_peel] at h
    split_ifs at h with hle hodd
    cases hrec : validate_and_peel ((y - 3 ^ (k + 1)) / 2 ^ count_div_by_2 (y - 3 ^ (k + 1))) k with
    | none => simp [hrec] at h
    | some val =>
      rcases val with ⟨tl, tot_tl⟩
      simp only [hrec, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      obtain ⟨hlen_tl, hpos_tl, hy_next_eq, htot_tl⟩ :=
        validate_and_peel_sound k _ tl tot_tl hrec
      set y_new := y - 3 ^ (k + 1)
      set a := count_div_by_2 y_new
      have hy_new_ne0 : y_new ≠ 0 := by omega
      have hdvd2 : 2 ∣ y_new := by omega
      have ha_pos : 1 ≤ a :=
        Nat.Prime.factorization_pos_of_dvd Nat.prime_two hy_new_ne0 hdvd2
      have hdvd_pow : 2 ^ a ∣ y_new := Nat.ordProj_dvd y_new 2
      have hy_new_eq : y_new = 2 ^ a * build_intercept tl := by
        calc y_new = 2 ^ a * (y_new / 2 ^ a) := (Nat.mul_div_cancel' hdvd_pow).symm
          _ = 2 ^ a * build_intercept tl := by rw [hy_next_eq]
      have hy_eq : y = build_intercept (a :: tl) := by
        simp only [build_intercept, hlen_tl]
        omega
      refine ⟨by simp [hlen_tl], ?_, hy_eq, ?_⟩
      · intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact ha_pos
        · exact hpos_tl z hz
      · simp [List.sum_cons, htot_tl, add_comm]

-- ============================================================================
-- SECTION 12: Safe Decoder Bridge & 2-Step Sharpened ils1b Growth Bound
-- ============================================================================

/-- Safe Option Nat version of count_div_by_2_in_recursive_lift. -/
def safe_count_div_by_2_in_recursive_lift (y_intercept : Nat) (starting_pow_3 : Nat) : Option Nat :=
  let rec aux (y : Nat) (pow_3 : Nat) (tot : Nat) : Option Nat :=
    if pow_3 < 1 then
      if y = 1 then
        some tot
      else
        none
    else if y ≤ 3 ^ pow_3 then
      none
    else
      let y_new := y - 3 ^ pow_3
      if y_new % 2 = 1 then
        none
      else
        let pow_2 := count_div_by_2 y_new
        let y_next := y_new / (2 ^ pow_2)
        if y_next < 1 then
          none
        else
          aux y_next (pow_3 - 1) (tot + pow_2)
  if starting_pow_3 < 1 then
    none
  else
    aux y_intercept (starting_pow_3 - 1) 0

lemma safe_aux_eq_validate (k : Nat) :
    ∀ (y tot : Nat),
      safe_count_div_by_2_in_recursive_lift.aux y k tot =
      (validate_and_peel y k).map (fun p => tot + p.2) := by
  induction k with
  | zero =>
    intro y tot
    rw [safe_count_div_by_2_in_recursive_lift.aux, ite_eq_left (by decide)]
    simp only [validate_and_peel]
    split_ifs <;> simp
  | succ k ih =>
    intro y tot
    rw [safe_count_div_by_2_in_recursive_lift.aux]
    simp only [validate_and_peel]
    have hnotlt1 : ¬ (k + 1 < 1) := by omega
    rw [ite_eq_right hnotlt1]
    split_ifs with hle hodd hnext
    · rfl
    · rfl
    · exfalso
      set y_new := y - 3 ^ (k + 1)
      set pow_2 := count_div_by_2 y_new
      have hy_new_pos : 0 < y_new := by omega
      have hdvd : 2 ^ pow_2 ∣ y_new := Nat.ordProj_dvd y_new 2
      have hy_next_pos : 1 ≤ y_new / 2 ^ pow_2 :=
        Nat.div_pos (Nat.le_of_dvd hy_new_pos hdvd) (by positivity)
      omega
    · set y_new := y - 3 ^ (k + 1)
      set pow_2 := count_div_by_2 y_new
      set y_next := y_new / (2 ^ pow_2)
      rw [Nat.add_sub_cancel, ih y_next (tot + pow_2)]
      cases hval : validate_and_peel y_next k with
      | none => simp
      | some p =>
        simp only [Option.map_some]
        ring

/-- Bridge Theorem: For any n ≥ 1, safe_count_div_by_2_in_recursive_lift y n equals
(validate_and_peel y (n - 1)).map Prod.snd. -/
theorem safe_count_eq_validate_and_peel (y n : Nat) (hn : 1 ≤ n) :
    safe_count_div_by_2_in_recursive_lift y n =
    (validate_and_peel y (n - 1)).map Prod.snd := by
  simp only [safe_count_div_by_2_in_recursive_lift, ite_eq_right (by omega : ¬ (n < 1))]
  rw [safe_aux_eq_validate (n - 1) y 0]
  cases validate_and_peel y (n - 1) <;> simp

lemma step_le_sixteen_fifths_of_odd_ge_five {y v m : Nat}
    (hy : y = 2 ^ v * m) (hm_odd : m % 2 = 1) (hm5 : 5 ≤ m) :
    5 * (3 * y + ils1b y) ≤ 16 * y := by
  have hval : count_div_by_2 y = v := by
    rw [hy]
    exact count_div_by_2_two_pow_mul hm_odd
  have hils : 5 * ils1b y ≤ y := by
    calc 5 * ils1b y
        = 2 ^ v * 5 := by simp [ils1b, hval]; ring
      _ ≤ 2 ^ v * m := Nat.mul_le_mul_left (2 ^ v) hm5
      _ = y := hy.symm
  omega

/-- Theorem (2-Step Sharpened ils1b Growth Bound):
Whenever BOTH y and y₁ = 3 * y + ils1b(y) are unterminated (¬ is_pow_two),
two consecutive lifted steps satisfy 3 * y₂ ≤ 32 * y (i.e. y₂ ≤ (32 / 3) * y),
strictly sharpening the naive squared bound (10 / 3)^2 = 100 / 9. -/
theorem two_step_sharpened_growth_bound
    {y : Nat} (hy : y ≠ 0)
    (hnot2_y : ¬ is_pow_two y)
    (hnot2_y₁ : ¬ is_pow_two (3 * y + ils1b y)) :
    let y₁ := 3 * y + ils1b y
    let y₂ := 3 * y₁ + ils1b y₁
    3 * y₂ ≤ 32 * y := by
  intro y₁ y₂
  set v := count_div_by_2 y
  rcases Nat.ordProj_dvd y 2 with ⟨m, hm⟩
  have hm_odd : m % 2 = 1 := by
    by_contra h
    have hm_even : 2 ∣ m := by omega
    rcases hm_even with ⟨r, rfl⟩
    have hr0 : r ≠ 0 := by intro hr; subst hr; simp only [mul_zero] at hm; exact hy hm
    have hge : v + 1 ≤ count_div_by_2 (2 ^ (v + 1) * r) := by
      have h2v1 : (2 : Nat) ^ (v + 1) ≠ 0 := by simp
      unfold count_div_by_2
      rw [Nat.factorization_mul h2v1 hr0, Finsupp.add_apply,
          Nat.Prime.factorization_pow Nat.prime_two]
      simp
    have heq : y = 2 ^ (v + 1) * r := by rw [hm]; dsimp [v, count_div_by_2]; ring
    rw [← heq] at hge
    omega
  have hm_ne1 : m ≠ 1 := by
    intro hm1
    apply hnot2_y
    exact ⟨v, by rw [hm, hm1, mul_one]; rfl⟩
  have hm_ge3 : 3 ≤ m := by omega
  by_cases hm3 : m = 3
  · have hy_eq : y = 2 ^ v * 3 := by rw [hm, hm3]; rfl
    have hils_y : ils1b y = 2 ^ v := by
      unfold ils1b
      rw [hy_eq, count_div_by_2_two_pow_mul (by decide : 3 % 2 = 1)]
    have hy₁_eq : y₁ = 2 ^ (v + 1) * 5 := by
      dsimp only [y₁]
      rw [hils_y, hy_eq, pow_succ']
      ring
    have hils_y₁ : ils1b y₁ = 2 ^ (v + 1) := by
      simp [ils1b, hy₁_eq, count_div_by_2_two_pow_mul (by decide : 5 % 2 = 1)]
    dsimp only [y₂]
    rw [hils_y₁, hy₁_eq, hy_eq, pow_succ']
    ring_nf
    omega
  · have hm5 : 5 ≤ m := by omega
    have hstep1 : 5 * y₁ ≤ 16 * y := step_le_sixteen_fifths_of_odd_ge_five hm hm_odd hm5
    have hy₁_ne0 : y₁ ≠ 0 := by simp only [y₁]; omega
    obtain ⟨_, hstep2, _⟩ := single_step_growth_squeeze hy₁_ne0 hnot2_y₁
    omega

-- ============================================================================
-- SECTION 13: 2-Step Sharpened Cycle Density Corollary (3^k * 2^I ≤ 32^k)
-- ============================================================================

/-- Multi-step 2-pair growth bound: across 2 * k unterminated steps (k ≥ 1),
3^k * y_{2*k} ≤ 32^k * x (i.e. y_{2*k} ≤ (32 / 3)^k * x). -/
theorem unterminated_even_orbit_sharpened_bound
    (x k : Nat) (hx : x ≠ 0) (hk : 1 ≤ k)
    (hunterm : ∀ r < 2 * k, ¬ is_pow_two (trace_state x r).1) :
    3 ^ k * (trace_state x (2 * k)).1 ≤ 32 ^ k * x := by
  induction k with
  | zero => omega
  | succ k ih =>
    have hy_ne0 : (trace_state x (2 * k)).1 ≠ 0 := trace_y_ne_zero x hx (2 * k)
    have hnot2_0 : ¬ is_pow_two (trace_state x (2 * k)).1 :=
      hunterm (2 * k) (by omega)
    have hnot2_1 : ¬ is_pow_two (3 * (trace_state x (2 * k)).1
      + ils1b (trace_state x (2 * k)).1) := by
      have hstep1_eq : 3 * (trace_state x (2 * k)).1 + ils1b (trace_state x (2 * k)).1 =
          (trace_state x (2 * k + 1)).1 := rfl
      rw [hstep1_eq]
      exact hunterm (2 * k + 1) (by omega)
    have hpair := two_step_sharpened_growth_bound hy_ne0 hnot2_0 hnot2_1
    dsimp only at hpair
    have htwo_steps : (trace_state x (2 * (k + 1))).1 =
        3 * (3 * (trace_state x (2 * k)).1 + ils1b (trace_state x (2 * k)).1) +
        ils1b (3 * (trace_state x (2 * k)).1 + ils1b (trace_state x (2 * k)).1) := by
      have heq : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [heq]
      rfl
    rw [htwo_steps]
    by_cases hk0 : k = 0
    · subst hk0
      simpa [trace_state] using hpair
    · have hk1 : 1 ≤ k := by omega
      have hunterm_prev : ∀ r < 2 * k, ¬ is_pow_two (trace_state x r).1 :=
        fun r hr => hunterm r (by omega)
      have hprev := ih hk1 hunterm_prev
      calc 3 ^ (k + 1) *
            (3 * (3 * (trace_state x (2 * k)).1 + ils1b (trace_state x (2 * k)).1) +
            ils1b (3 * (trace_state x (2 * k)).1 + ils1b (trace_state x (2 * k)).1))
          = 3 ^ k * (3 * (3 * (3 * (trace_state x (2 * k)).1 + ils1b (trace_state x (2 * k)).1) +
            ils1b (3 * (trace_state x (2 * k)).1 + ils1b (trace_state x (2 * k)).1))) := by ring
        _ ≤ 3 ^ k * (32 * (trace_state x (2 * k)).1) := Nat.mul_le_mul_left (3 ^ k) hpair
        _ = 32 * (3 ^ k * (trace_state x (2 * k)).1) := by ring
        _ ≤ 32 * (32 ^ k * x) := Nat.mul_le_mul_left 32 hprev
        _ = 32 ^ (k + 1) * x := by ring

/-- Corollary (2-Step Sharpened Cycle Density Window for Even-Length Cycles n = 2k):
If a non-trivial odd cycle of even length n = 2k (k ≥ 1, x > 1) satisfies
y_{2k} = 2^I * x, then:
1) 9^k < 2^I
2) 3^k * 2^I ≤ 32^k
3) 9^k * 2^(2 * I) ≤ 1024^k -/
theorem nontrivial_even_cycle_sharpened_density
    (x k I : Nat) (hx_gt : 1 < x) (hk : 1 ≤ k)
    (hunterm : ∀ r < 2 * k, ¬ is_pow_two (trace_state x r).1)
    (hcycle : (trace_state x (2 * k)).1 = 2 ^ I * x) :
    9 ^ k < 2 ^ I ∧ 3 ^ k * 2 ^ I ≤ 32 ^ k ∧ 9 ^ k * 2 ^ (2 * I) ≤ 1024 ^ k := by
  have hx_pos : 0 < x := by omega
  have hx_ne0 : x ≠ 0 := by omega
  obtain ⟨hlo, _⟩ :=
    nontrivial_cycle_density_window x (2 * k) I hx_gt (by omega) hunterm hcycle
  have hlo9 : 9 ^ k < 2 ^ I := by
    have h9 : 9 ^ k = 3 ^ (2 * k) := by
      calc 9 ^ k = (3 ^ 2) ^ k := by norm_num
        _ = 3 ^ (2 * k) := by rw [← pow_mul]
    rwa [h9]
  have hhi := unterminated_even_orbit_sharpened_bound x k hx_ne0 hk hunterm
  rw [hcycle] at hhi
  have hhi32 : 3 ^ k * 2 ^ I ≤ 32 ^ k := by
    have hreassoc : (3 ^ k * 2 ^ I) * x ≤ 32 ^ k * x := by
      calc (3 ^ k * 2 ^ I) * x = 3 ^ k * (2 ^ I * x) := by ring
        _ ≤ 32 ^ k * x := hhi
    exact Nat.le_of_mul_le_mul_right hreassoc hx_pos
  have hsq : 9 ^ k * 2 ^ (2 * I) ≤ 1024 ^ k := by
    have hpow2 : (3 ^ k * 2 ^ I) ^ 2 ≤ (32 ^ k) ^ 2 := Nat.pow_le_pow_left hhi32 2
    have hlhs : (3 ^ k * 2 ^ I) ^ 2 = 9 ^ k * 2 ^ (2 * I) := by
      calc (3 ^ k * 2 ^ I) ^ 2
          = (3 ^ k) ^ 2 * (2 ^ I) ^ 2 := by ring
        _ = (3 ^ 2) ^ k * 2 ^ (I * 2) := by rw [← pow_mul, ← pow_mul, ← pow_mul, mul_comm k 2]
        _ = 9 ^ k * 2 ^ (2 * I) := by norm_num [mul_comm I 2]
    have hrhs : (32 ^ k) ^ 2 = 1024 ^ k := by
      calc (32 ^ k) ^ 2 = (32 ^ 2) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm k 2]
        _ = 1024 ^ k := by norm_num
    rwa [hlhs, hrhs] at hpow2
  exact ⟨hlo9, hhi32, hsq⟩

-- ============================================================================
-- SECTION 14: Executable Examples & Master #check Reference Index
-- ============================================================================

#eval make_boutique_intercept [1, 2, 3]          -- some (133, 4)
#eval safe_count_div_by_2_in_recursive_lift 133 4 -- some 6
#eval safe_count_div_by_2_in_recursive_lift 135 4 -- none
#eval decode_list 133 3                           -- [1, 2, 3]

section ReferenceChecks

-- 1. Affine Invariant & Bijective Decoding
#check @trace_state_affine
#check @forward_trajectory_produces_build_intercept
#check @count_div_by_2_in_recursive_lift_reversible
#check @decode_list_build_intercept
#check @build_intercept_injective_of_length_eq
#check @starting_x_unique_from_y_and_b

-- 2. Strict Validation & Boutique Constructors
#check @validate_boutique_intercept
#check @validate_and_peel_sound
#check @safe_count_eq_validate_and_peel

-- 3. Parameter Necessity & Euler Totient Periodicity
#check @witness_b_185_two_slopes
#check @euler_totient_preserves_odd_seed

-- 4. Infinite Cycle Tower Reduction
#check @tower_intercept_geometric_identity
#check @tower_intercept_is_peelable
#check @tower_divisibility_iff_base_divisibility

-- 5. ils1b Growth Squeeze & Cycle Elimination
#check @three_mul_ils1b_le_of_not_pow_two
#check @trivial_loop_step_exact
#check @unterminated_orbit_growth_squeeze
#check @intercept_upper_bound_from_squeeze
#check @nontrivial_cycle_density_window
#check @two_step_sharpened_growth_bound
#check @nontrivial_even_cycle_sharpened_density
#check @no_nontrivial_cycle_of_finite_check
#check @no_nontrivial_1_cycle
#check @no_nontrivial_2_cycle
#check @no_nontrivial_3_cycle
#check @no_nontrivial_4_cycle
#check @no_nontrivial_5_cycle
#check @no_nontrivial_6_cycle

end ReferenceChecks

end LiftedCollatz
