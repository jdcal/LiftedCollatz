```markdown
# Lifted Collatz Trajectories in Lean 4

A formalization of division-free ("lifted") Collatz dynamics in Lean 4 and Mathlib, proving trajectory reversibility, Euler totient periodicity, infinite cycle tower reduction, sharpened 2-step growth bounds, and the non-existence of non-trivial odd Collatz cycles of length $n \le 6$.

## Mathematical Overview

Instead of dividing by $2$ at every even step, the **lifted Collatz map** tracks powers of $2$ multiplicatively using the Isolated Least Significant 1-Bit $\mathrm{ils1b}(y) = 2^{v_2(y)}$:

$$y_{k+1} = 3 y_k + \mathrm{ils1b}(y_k), \qquad b_{k+1} = 3 b_k + \mathrm{ils1b}(y_k)$$

Every $n$-step trajectory satisfies the exact affine invariant $y_n = 3^n x + b_n$. A trajectory reaches $1$ in the standard Collatz map if and only if $y_n = 2^t$ (`is_pow_two`) for some $n$.

## Formalized Results

### 1. Affine Invariant & Bijective Intercept Decoding (`Section 3`)

* **`trace_state_affine`**: Proves $y_n = 3^n x + b_n$ for all $n \in \mathbb{N}$ starting from $(x, 0)$.
* **`forward_trajectory_produces_build_intercept` & `decode_list_build_intercept`**: Establishes an exact bijection between step-by-step 2-adic jump lists $[a_1, \dots, a_{n-1}]$ ($a_i \ge 1$) and polynomial $y$-intercepts $b = \mathrm{build\_intercept}([a_1, \dots, a_{n-1}])$.
* **`build_intercept_injective_of_length_eq` & `starting_x_unique_from_y_and_b`**: Proves unique recovery of both the jump history and the starting seed $x$ from $(y_n, b_n)$.

### 2. Parameter Necessity & Euler Totient Periodicity (`Section 4`)

* **`witness_b_185_two_slopes`**: Exhibits an explicit counterexample ($b = 185$) showing why fixing the starting power of $3$ is necessary for unique intercept decoding.
* **`euler_totient_preserves_odd_seed`**: Proves that shifting jump exponents by multiples of $\varphi(3^n) = 2 \cdot 3^{n-1}$ preserves the modular residue class of the starting seed $x$.

### 3. Growth Squeeze & Cycle Density Bounds (`Sections 5, 12, 13`)

* **`unterminated_orbit_growth_squeeze`**: Proves that every unterminated step satisfies $3 y_k < y_{k+1} \le \frac{10}{3} y_k$, yielding $3^n x < y_n \le \left(\frac{10}{3}\right)^n x$.
* **`nontrivial_cycle_density_window`**: Any non-trivial odd cycle ($x > 1$) of length $n$ with total 2-adic valuation $I$ satisfies $3^n < 2^I$ and $3^n \cdot 2^I \le 10^n$.
* **`two_step_sharpened_growth_bound` & `nontrivial_even_cycle_sharpened_density`**: Sharpens two consecutive unterminated steps from $\left(\frac{10}{3}\right)^2 = \frac{100}{9}$ down to $3 y_{k+2} \le 32 y_k$, tightening even-length cycle windows ($n = 2k$) to $9^k < 2^I$ and $3^k \cdot 2^I \le 32^k$.

### 4. Infinite Cycle Tower Reduction (`Section 7`)

* **`tower_intercept_geometric_identity` & `tower_divisibility_iff_base_divisibility`**: Proves that repeating an $n$-step cycle block $k$ times scales the divisibility condition by a geometric series, showing $(2^{kI} - 3^{kn}) \mid \mathrm{tower\_intercept\_k} \iff (2^I - 3^n) \mid b$.

### 5. Non-Trivial Cycle Elimination for $n \le 6$ (`Sections 6, 8, 9, 10`)

* **`no_nontrivial_1_cycle` through `no_nontrivial_6_cycle`**: Eliminates all non-trivial odd cycles of lengths $1, 2, 3, 4, 5,$ and $6$ by combining the density window bounds with `no_nontrivial_cycle_of_finite_check`.

### 6. Verified Peelability Validator (`Sections 11, 12`)

* **`validate_boutique_intercept` & `validate_and_peel_sound`**: Provides a decidable `Option`-returning validator `validate_and_peel` proven sound and complete against `build_intercept`.

The peel algorithm decodes the $y$-intercept, $b$, to obtain the lift list / jump list.

### 7. Commentary and Notes from Gemini

I had written proof-of-concept code in Common Lisp. I wanted a more robust presentation of the ideas, and I wanted to learn more about Lean. I began writing experimental code and slowly pieced together enough Lean 4 code to allow Gemini to see my ideas. After showing Gemini the $y$-intercept's Horner-style expansion, its response was "Aha!". That was Nov 22, 2026. Today is Nov 25, 2026. Every theorem in this project was generated in cooperation with Gemini in those three days, with today being project and GitHub day.

I asked Gemini to describe the project's contents:

Here is a breakdown of what is genuinely novel or distinctive about your formalization, how it connects to the literature, and where you can take it into modern Collatz research.

#### 1. Is the division-free $\mathbb{N}$ implementation unique, and what does it make easy?

Yes—most existing Lean 4 Collatz formalizations work with the halved Syracuse map $S(n) = (3n+1)/2^{v_2(3n+1)}$ using division (`/`), whereas keeping powers of $2$ un-divided in $\mathbb{N}$ ($y_{k+1} = 3y_k + 2^{v_2(y_k)}$) is a distinct design choice. Because natural-number division in Lean/Mathlib is truncating ($5 / 2 = 2$) and requires constant divisibility side-conditions ($2^k \mid \dots$), division-free trajectories avoid rational arithmetic ($\mathbb{Q}$) and integer division entirely:

* **The Affine Invariant (`trace_state_affine`)**: Proving $y_n = 3^n x + b_n$ becomes a three-line induction with `ring` instead of clearing denominators across $n$ steps.
* **The Growth Squeeze (`unterminated_orbit_growth_squeeze` & `two_step_sharpened_growth_bound`)**: Inequalities like $3 \cdot y_2 \le 32 \cdot y$ stay purely in $\mathbb{N}$, letting `omega` and `positivity` close goals without casting to $\mathbb{Q}$ or $\mathbb{R}$.
* **Exact Peelability (`validate_and_peel`)**: Because $b_n$ is never divided out, the $2$-adic jumps $[a_1, \dots, a_{n-1}]$ remain literally encoded as the binary bit-gaps inside the single natural number $b_n$.

#### 2. Is the encoding of the jump list inside $b$ in the literature?

Yes—the formula $b_n = \sum_{i=1}^n 3^{n-i} 2^{A_{i-1}}$ (where $A_k = a_1 + \dots + a_k$ are the partial sums of your jump list) is a classical identity in Collatz literature, though treating $b_n$ itself as a self-delimiting data structure via `validate_and_peel` is a neat algorithmic framing.

* **What it's called in the literature**: In standard papers, your "jump list" $[a_1, \dots, a_{n-1}]$ is called the parity vector or $2$-adic valuation sequence $(v_2(3x_i + 1))_{i=0}^{n-1}$, and the affine map $T^{(n)}(x) = \frac{3^n x + b_n}{2^I}$ is called the accelerated Collatz affine map (or Syracuse trajectory polynomial).
* **Key Literature References**:
  * **Riho Terras (1976)**, *"A stopping time problem on the positive integers"* (*Acta Arithmetica* 30, 241–252) — introduced parity vectors and the affine representation $(3^n x + b_n)/2^I$ to prove almost all orbits have finite stopping time.
  * **Jeffrey C. Lagarias (1985)**, *"The $3x + 1$ Problem and Its Generalizations"* (*American Mathematical Monthly* 92, 3–23) — the standard reference giving the explicit closed form $b_n = \sum_{i=0}^{n-1} 3^{n-1-i} 2^{a_1 + \dots + a_i}$ and analyzing its $2$-adic and $3$-adic properties.
  * **Günther J. Wirsching (1998)**, *The Dynamical System Generated by the $3n+1$ Function* (*Lecture Notes in Mathematics* 1681, Springer) — studies the "predecessor tree" and unique decoding of jump sequences from $b_n$ (which corresponds directly to your `decode_list_build_intercept` and `build_intercept_injective_of_length_eq`).

#### 3. What is the most recent result currently in your codebase, and what modern results can we reproduce next?

##### Where your current codebase sits chronologically

* **1976–1978 (Terras / Steiner)**: The affine cycle equation $(2^I - 3^n)x = b_n$ and elimination of $1$-cycles ($m=1$ local minima).
* **1985–1990s (Lagarias / Eliahou / Crandall)**: Density window bounds ($3^n < 2^I$) and small-step cycle elimination ($n \le 6$), which your Sections 6–10 formalize completely from scratch.
* **2020s–2026 Lean Formalization Frontier**: Building verified, kernel-checked decision procedures (`validate_and_peel`, `no_nontrivial_cycle_of_finite_check`) and sharpened multi-step block inequalities (`two_step_sharpened_growth_bound`) in Lean 4 is very much aligned with recent Lean 4 Collatz projects (such as the Collatz / Syracuse Conditional Cycles formalization and the Collatz Conjecture Challenge).

##### Modern results we can formalize next using your existing machinery

1. **Christian Hercher (2022/2023)**, *"There are no Collatz $m$-cycles with $m \le 91$"* (`arXiv:2201.00406`) & **Simons–de Weger (2005)**:
   * Instead of bounding total odd steps $n$, modern cycle bounds group consecutive $a_i = 1$ steps into "waves" or "$m$-cycles" (where $m$ is the number of local minima in a cycle).
   * Using your `build_intercept` and `tower_intercept_geometric_identity`, we can formalize Steiner's Theorem (1977) (no non-trivial $1$-cycle, i.e., a cycle with a single run of $a_i = 1$ followed by a drop $a_m \ge 2$, which reduces to solving $2^I - 3^n = 2^a - 1$) and extend your finite-check engine to Simons–de Weger's $m$-cycle inequality.
2. **Terence Tao (2019/2022)**, *"Almost all orbits of the Collatz map attain almost bounded values"* (*Forum of Mathematics, Pi*):
   * While Tao's full proof uses logarithmic density and Syracuse random walks on $\mathbb{Z}/3^n\mathbb{Z}$, your Section 4 (`euler_totient_preserves_odd_seed`) already proves the foundational modular periodicity on $\mathbb{Z}/3^n\mathbb{Z}$ that makes Syracuse measure-preservation work.
3. **Sharpening `no_nontrivial_cycle_of_finite_check` with your Section 13 bound**:
   * Right now, `no_nontrivial_cycle_of_finite_check` uses the single-step bound $3^n \cdot 2^I \le 10^n$. Plugging in your new Section 13 (`nontrivial_even_cycle_sharpened_density`) ($3^k \cdot 2^I \le 32^k$) shrinks the candidate `cand_I` window for all even cycle lengths ($n = 8, 10, 12, \dots$), letting Lean check larger cycles much faster.

##### How Your Code Matches Eliahou's Result

In a nontrivial cycle of $n$ odd steps and $S$ total divisions by $2$ (which corresponds to $S + n$ total standard Collatz steps), the cycle equation in your lifted coordinates is:

$$y_n = 3^n x + b_n = 2^S x \implies (2^S - 3^n)x = b_n$$

In Shalom Eliahou's 1993 paper (*"The 3x+1 problem: new lower bounds on nontrivial cycle lengths"*, *Discrete Mathematics* 118), the ratio of total divisions by $2$ to odd steps, $S/n$, satisfies the logarithmic window:

$$\frac{\ln 3}{\ln 2} < \frac{S}{n} < \frac{\ln(3 + 1/x_{\min})}{\ln 2}$$

In your `LiftedCollatz.lean` file, this constraint is expressed in $\mathbb{N}$ without floating-point logarithms:

* **Section 5 (`nontrivial_cycle_density_window`)**: Establishes $3^n < 2^I$ and $3^n \cdot 2^I \le 10^n$, corresponding to:

  $$\frac{\ln 3}{\ln 2} < \frac{I}{n} \le \frac{\ln(10/3)}{\ln 2}$$

  (and for total Collatz steps $N = I + n$, $\frac{\ln 3}{\ln 2} < \frac{N}{n} \le \frac{\ln(20/3)}{\ln 2}$).
* **Section 13 (`nontrivial_even_cycle_sharpened_density`)**: Tightens two-step growth bounds ($3 \to 5$ gives $\frac{10}{3} \cdot \frac{16}{5} = \frac{32}{3} < \frac{100}{9}$) for even-length cycles $n = 2k$, sharpening the upper bound from $3^{2k} \cdot 2^I \le 100^k$ to $3^k \cdot 2^I \le 32^k$ (i.e., $2^I \le (32/3)^k$ instead of $(100/9)^k$), alongside continued-fraction lower-bound methods reaching $1.7087915 \times 10^7$ odd steps.

##### Other Classical Results in Your File

In addition to Eliahou's density window, your module also independently formalizes:

* Steiner's / Böhm–Sontacchi's Cycle Equation (`trace_state_affine` and `build_intercept` in Sections 1 & 3).
* Small-Cycle Elimination for $n \le 6$ (`no_nontrivial_1_cycle` through `no_nontrivial_6_cycle` in Sections 6–10).

## Building the Project

```bash
lake exe cache get
lake build

```

```

```