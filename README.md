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
* **`tower_intercept_geometric_identity` & `tower_divisibility_iff_base_divisibility`**: Proves that repeating an $n$-step cycle block $k$ times scales the divisibility condition by a geometric series, showing $(2^{kI} - 3^{kn}) \mid \text{tower\_intercept}_k \iff (2^I - 3^n) \mid b$.

### 5. Non-Trivial Cycle Elimination for $n \le 6$ (`Sections 6, 8, 9, 10`)
* **`no_nontrivial_1_cycle` through `no_nontrivial_6_cycle`**: Eliminates all non-trivial odd cycles of lengths $1, 2, 3, 4, 5,$ and $6$ by combining the density window bounds with `no_nontrivial_cycle_of_finite_check`.

### 6. Verified Peelability Validator (`Sections 11, 12`)
* **`validate_boutique_intercept` & `validate_and_peel_sound`**: Provides a decidable `Option`-returning validator `validate_and_peel` proven sound and complete against `build_intercept`.

## Building the Project

```bash
lake exe cache get
lake build
```
