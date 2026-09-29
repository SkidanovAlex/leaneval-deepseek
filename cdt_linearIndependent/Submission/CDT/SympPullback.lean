import Mathlib
import Submission.CDT.SympZagier
import Submission.CDT.ZagierH
import Submission.Commons.RingTheory.PowerSeries.iterate_subst_deriv_scaled
import Submission.Commons.RingTheory.PowerSeries.iterate_derivative_coeff_fact

/-!
# Route (b): the pull-back of `HA_ode` under `x ↦ φ(x) = x/(x−1)` and the
order-4 `x`-ODE of `F = H_A + H_A∘φ`

Second line toward the paper's eq. (explicitode) (`GA_odeLHS (Sym⁺H_A) = 0`,
module `Submission.CDT.SympExplicitode`): instead of expanding the descent
coefficients of `G_A` (route (a)), push `HA_ode` through the Möbius map
`φ`.  The engine: `H_A` is killed by the order-2 `x`-ODE
`a₂·H_A″ + a₁·H_A′ + a₀·H_A = 0` (`HA_ode`, `ZagierH`), and the
symmetrization identity `(Sym⁺H_A)∘y = H_A + H_A∘φ`
(`sympSym_subst`) exhibits the symmetrized series as the descent of the
sum `F = H_A + H_A∘φ` of two order-2-ODE-killed summands.

**Proved here (summand 1)**: the pull-back of the ODE under substitution
`x ↦ φ(x)`.  For `H̃ := H_A∘φ`, and the scaled derivative
`E(f) := ψ·f′` with `ψ := −(X−1)² = 1/φ′` (`sympPhi_deriv_mul_PBpsi`:
`φ′·ψ = 1`, from `sympPhi_deriv_eq`: `φ′ = −((X−1)⁻¹)²`),

```lean
theorem HA_subst_sympPhi_pullback_ode :
  (a₂∘φ)·E²(H̃) + (a₁∘φ)·E(H̃) + (a₀∘φ)·H̃ = 0
```

Proof: the commons law `iterate_subst_deriv_scaled` gives
`Eⁱ(H̃) = (H_A⁽ⁱ⁾)∘φ`, the substitution ring-hom (`subst_mul`, `subst_add`)
gathers the three terms into `(a₂·H_A″ + a₁·H_A′ + a₀·H_A)∘φ`, which is
`(HA_odeLHS H_A)∘φ = 0` by `HA_ode`.

**Proved here (the order-4 `x`-ODE for `F`, Wronskian form)**: the
5×5-determinant Wronskian operator `wr4 u v f` (rows `u, u′, v, v′, f`,
columns the derivatives `0..4`, so `wr4 u v f = Σⱼ cⱼ(x)·f⁽ʲ⁾` for
determinant coefficients `cⱼ ∈ ℚ[[x]]`) kills `u, v, u′, v′` by the
duplicate-row law (`wr4_left/right/left_deriv/right_deriv`,
`Matrix.det_zero_of_row_eq`) and kills `u + v` by the row-additivity law
(`wr4_sum`, `Matrix.det_updateRow_add` + `PSdd_iterate_add`).  With
`u := H_A`, `v := H_A∘φ` (so `F = H_A + H_A∘φ` is killed):

```lean
theorem HAF_wronskian_ode : wr4 HA (HA.subst sympPhi) HAF = 0
```

**Proved here (monic reduction)**: the leading coefficient `wr4Lead u v`
(the 4×4 Wronskian determinant of `u, u′, v, v′`) and the
monic-normalized operator `wr4Monic u v f := wr4Lead(u,v)⁻¹ · wr4(u,v)(f)`;
it kills `u, v, u′, v′` and `u + v` (`wr4Monic_left/right/left_deriv/
right_deriv/sum`), and in particular

```lean
theorem HAF_wronskian_monic_ode : wr4Monic HA (HA.subst sympPhi) HAF = 0
```

**Proved here (the Laplace row expansion)** — the cofactor expansion of
the 5×5 Wronskian determinant along its `f`-row: with
`wr4Minor u v j := det` of the 4×4 matrix (rows `u,u′,v,v′`, columns
`Fin 5 ∖ {j}`) one has (`Matrix.det_succ_row`, the last-column minor is the
leading coefficient — `wr4Minor_last`),

```lean
lemma wr4_expand (u v f) :
  wr4 u v f = ∑ j : Fin 5, (−1)^{4+j} · f⁽ʲ⁾ · wr4Minor u v j

lemma wr4_expand_monic (u v f) :
  wr4 u v f = wr4Lead u v · f⁗ + Σₖ₌₀³ (−1)^{4+k}·wr4Minor u v k · f⁽ᵏ⁾
```

so `wr4Monic u v f = f⁗ + Σₖ₌₀³ sₖ·f⁽ᵏ⁾` with `sₖ := (−1)^{4+k}·
wr4Lead(u,v)⁻¹·wr4Minor u v k` — the Wronskian operator is literally monic
(leading coefficient `1`).

**Remaining steps** (updated): the two items listed below in earlier
revisions are now resolved or superseded by the paragraphs that follow
("Step (1) of the push-down — DONE", "Course correction …", "Step (2) is
DONE …"), which are the authoritative record.  In short: item 1 (expressing
the `wr4Minor` through order-2 data) was never needed (the minors are used
only through `wr4_expand_monic`); item 2's literal reading — "substitute
the chain rules into the *monic* `x`-ODE and read off `(cₖ∘y)`" — is
**false** (the monic-normalized `D`-form coefficients `sⱼ` are genuine
`ℚ⟦x⟧`-series, not `cₖ∘y`; the two relations among `Wₖ = (G_A⁽ᵏ⁾∘y)` are
not proportional).  What remains for the push-down is the
`ℚ(x)`-elimination: with `y = x²/(x−1) ∈ ℚ(x)` and every `Wₖ ∈ V :=
span_{ℚ(x)}{H_A, H_A′, H_A∘φ, (H_A∘φ)′}` (dim 4), prove that the unique
`ℚ(x)`-relation of `W₀..W₄` is `Σₖ (cₖ∘y)·Wₖ = 0` (verified numerically
to degree 12 with the descent `g₀..g₁₁`), i.e. prove
`(GA_odeLHS (Sym⁺H_A)).subst sympY = 0` and conclude by
`symp_subst_y_injective`.

**Step (1) of the push-down — DONE (see §"Faà di Bruno …" at the end of
this module)**: the iterated chain rule to orders `1..4`: with `F = G∘y`,
the `x`-derivatives `DⁱF` are expanded through the composed `y`-derivatives
`(DᵏG)∘y` with coefficients polynomial in `y′, y″, …`
(`d_subst_chain`/`d2_subst_chain`/`d3_subst_chain`/`d4_subst_chain`, and
their `G := sympSym HA`, `F = HAF` instances `HAF_d2/d3/d4_chain`).

**Course correction (numerically verified against the paper's `cᵢ`, all
orders `≤ 12`) — what step (3) CANNOT be.**  The naive plan — substitute
the chain-rule expansions into the monic `x`-ODE and compare the resulting
coefficient `Aₖ(x)` of `(G_A⁽ᵏ⁾∘y)` with `(cₖ∘y)(x)` — *fails*: the `Aₖ`
one gets from the Wronskian data are NOT equal to `cₖ∘y` (e.g. the `F`-
coefficient of the pushed-down monic ODE, `s₀ = wr4Lead⁻¹·minor₀`, is a
genuine rational function of `x` with leading constant `≠ −54 = c₀(y(0))`).
  The correct mechanism is the *`ℚ(x)`-elimination in the four-dimensional
solution space*: since `y = x²/(x−1)` is a *rational* function and each
`Wₖ = (G_A⁽ᵏ⁾∘y)` lies in `V := span_{ℚ(x)}{H_A, H_A′, H_A∘φ, (H_A∘φ)′}`
(dim 4, the solution space of the monic Wronskian `x`-ODE), the five
series `W₀..W₄` satisfy one `ℚ(x)`-linear relation; the claim is that this
relation is `Σₖ (cₖ∘y)·Wₖ = 0` (equivalently `W₄ = Σ_{k<4} (cₖ/c₄)(y(x))·
Wₖ`), from which the explicitode follows by composing back with the
injective substitution `Y ↦ y(X)`.  Verified numerically (descent
coefficients `g₀..g₁₁` + paper `cₖ`): `Σₖ (cₖ∘y)·Wₖ = 0` to degree 12.
  The chain-rule layer above is the input to that elimination (each
`DⁱF`, hence each `Wₖ` once divided by the appropriate power of
`y′ = X·unit`, is expressed through the four generators of `V`).
Step (2) is DONE in its un-normalized form: the expanded order-4 `x`-ODE
`wr4Lead·D⁴F + Σ_{k<4} (−1)^{4+k}·wr4Minor(u,v,k)·DⁱF = 0` is proved
(`HAF_wronskian_expanded_ode`; no division needed — it is exactly the
`wr4_expand_monic` Laplace expansion killing `F`, and it is the form into
which the chain rules `HAF_di_chain` are substituted).  The *monic*
normalization is also now complete: `wr4Lead_constantCoeff` evaluates the
constant term of the leading Wronskian coefficient (the `4×4` Wronskian
determinant of `H_A, H_A′, H_A∘φ, (H_A∘φ)′` at `0`) as `37290132 ≠ 0`
(`cc_iter` = `j!·[x^j]` formula + the concrete determinant
`wr4LeadConstMat_det`), so `wr4Lead_isUnit` holds.

**Finding (numerical, all orders ≤ 20) — the monic-normalized D-form
coefficients do NOT surface the paper's `cₖ`; keep the un-normalized
expanded ODE as the master statement.**  Writing the monic `x`-ODE as
`D⁴F + Σ_{j<4} sⱼ·DʲF = 0` (`sⱼ := (−1)^{4+j}·wr4Lead⁻¹·wr4Minor(u,v,j)`),
one has `s₀(0) ≈ 14270 ≠ −54 = c₀(y(0))`, so `sⱼ ≠ (cⱼ∘y)`.  More
decisively, substituting the chain rules (`HAF_di_chain`) turns the monic
`x`-ODE into a relation `Σₖ Aₖ·Wₖ = 0` (`Wₖ := (G_A⁽ᵏ⁾∘y)`, `A₀ = s₀`,
`A₁ = s₁y′+s₂y″+s₃y‴+y⁗`, …) whose coefficient tuple is **not
proportional** (over `ℚ⟦x⟧`) to the `y`-ODE tuple `(cₖ∘y)`: both relations
kill `F`, but they are genuinely different power-series relations.  The
reason: the `Aₖ`/`sⱼ` are genuine `ℚ⟦x⟧`-series (the Wronskian data of the
non-rational series `u = H_A`), whereas `cₖ∘y ∈ ℚ(y(x)) ⊆ ℚ(x)` are
*rational functions* of `x`; over `ℚ(x)` the five `Wₖ` (all in the
four-dimensional space `V`) have a *unique* relation, and the `y`-ODE
relation is it.  Conclusion: the `y`-ODE is reached through the
`ℚ(x)`-elimination among `W₀..W₄` (equivalently through the
`E = (1/y′)D`-form, dividing by powers of `y′ = X·unit` where
`F′ = W₁·y′` is divisible), *not* through monic normalization of the
`D`-form Wronskian `x`-ODE; the expanded un-normalized ODE is the right
master statement to push down.

All declarations are fully proved (no axioms, no `sorry`).
-/

noncomputable section
open PowerSeries
namespace Submission.CDT

/-- derivative of `(X−1)⁻¹` is `−((X−1)⁻¹)²` -/
lemma XsubOne_inv_deriv : (PowerSeries.derivative (R := ℚ)) (((X : PowerSeries ℚ) - 1)⁻¹) =
    -((((X : PowerSeries ℚ) - 1)⁻¹) ^ 2) := by
  rw [PowerSeries.derivative_inv']
  simp

/-- `(X−1)` is a unit: `((X−1)⁻¹)·(X−1) = 1` -/
lemma XsubOne_unit_mul : (((X : PowerSeries ℚ) - 1)⁻¹) * ((X : PowerSeries ℚ) - 1) = 1 := by
  have hcc : PowerSeries.constantCoeff ((X : PowerSeries ℚ) - 1) ≠ 0 := by simp
  exact PowerSeries.inv_mul_cancel ((X : PowerSeries ℚ) - 1) hcc

/-- derivative of `φ = X·(X−1)⁻¹` is `−((X−1)⁻¹)²` -/
lemma sympPhi_deriv_eq : (PowerSeries.derivative (R := ℚ)) sympPhi =
    -((((X : PowerSeries ℚ) - 1)⁻¹) ^ 2) := by
  let W : PowerSeries ℚ := ((X : PowerSeries ℚ) - 1)⁻¹
  have hdef : sympPhi = X * W := by
    unfold sympPhi
    rfl
  have hXW : X * W = 1 + W := by
    have hWX0 : W * X - W = 1 := by
      calc
        W * X - W = W * ((X : PowerSeries ℚ) - 1) := by ring
        _ = 1 := XsubOne_unit_mul
    calc
      X * W = W * X := by ring
      _ = 1 + W := by
            calc
              W * X = (W * X - W) + W := by ring
              _ = 1 + W := by rw [hWX0]
  calc
    (PowerSeries.derivative (R := ℚ)) sympPhi = (PowerSeries.derivative (R := ℚ)) (X * W) := by rw [hdef]
    _ = X * (PowerSeries.derivative (R := ℚ)) W + W := by
          rw [Derivation.leibniz]
          simp
    _ = X * (-(W ^ 2)) + W := by
          have hW : (PowerSeries.derivative (R := ℚ)) W = -(W ^ 2) := by
            dsimp [W]
            exact XsubOne_inv_deriv
          rw [hW]
    _ = -W ^ 2 := by
          calc
            X * (-(W ^ 2)) + W = -(X * W * W) + W := by ring
            _ = -((1 + W) * W) + W := by rw [hXW]
            _ = -W ^ 2 := by ring

/-- the scaled-derivative multiplier `ψ = −(X−1)²`, an inverse of `φ′` -/
def PBpsi : PowerSeries ℚ := -((X : PowerSeries ℚ) - 1) ^ 2

/-- `φ′·ψ = 1` -/
lemma sympPhi_deriv_mul_PBpsi : (PowerSeries.derivative (R := ℚ)) sympPhi * PBpsi = 1 := by
  rw [sympPhi_deriv_eq]
  unfold PBpsi
  calc
    -((((X : PowerSeries ℚ) - 1)⁻¹) ^ 2) * (-((X : PowerSeries ℚ) - 1) ^ 2) = 1 := by
      have hcc : PowerSeries.constantCoeff ((X : PowerSeries ℚ) - 1) ≠ 0 := by simp
      have hcancel : ((((X : PowerSeries ℚ) - 1)⁻¹) ^ 2) * (((X : PowerSeries ℚ) - 1) ^ 2) = 1 := by
        rw [← mul_pow]
        rw [XsubOne_unit_mul]
        norm_num
      calc
        -((((X : PowerSeries ℚ) - 1)⁻¹) ^ 2) * (-((X : PowerSeries ℚ) - 1) ^ 2)
            = ((((X : PowerSeries ℚ) - 1)⁻¹) ^ 2) * (((X : PowerSeries ℚ) - 1) ^ 2) := by ring
        _ = 1 := hcancel

/-- `a₂(x) = X(1−X)(1−9X) = X − 10X² + 9X³`, the `y″`-coefficient of the ODE -/
def HA_a2 : PowerSeries ℚ := X - PowerSeries.C 10 * X ^ 2 + PowerSeries.C 9 * X ^ 3
/-- `a₁(x) = 1 − 20X + 27X²`, the `y′`-coefficient -/
def HA_a1 : PowerSeries ℚ := (1 : PowerSeries ℚ) - PowerSeries.C 20 * X + PowerSeries.C 27 * X ^ 2
/-- `a₀(x) = −3 + 9X`, the `y`-coefficient -/
def HA_a0 : PowerSeries ℚ := -PowerSeries.C 3 + PowerSeries.C 9 * X

/-- decomposition of the ODE operator into its three coefficient series -/
lemma HA_odeLHS_decomp (y : PowerSeries ℚ) :
    HA_odeLHS y = HA_a2 * (PowerSeries.derivative (R := ℚ) ((PowerSeries.derivative (R := ℚ)) y))
      + HA_a1 * (PowerSeries.derivative (R := ℚ)) y + HA_a0 * y := by
  unfold HA_odeLHS HA_a2 HA_a1 HA_a0
  ring

/-- the pull-back of `HA_ode` under `x ↦ φ(x)`: with `H̃ = H_A∘φ` and the
scaled derivative `E = ψ·d/dx` (`ψ = 1/φ′`), one has
`(a₂∘φ)·E²(H̃) + (a₁∘φ)·E(H̃) + (a₀∘φ)·H̃ = 0` — i.e. `H̃` satisfies the
ODE pulled back through the Möbius map `φ`. -/
theorem HA_subst_sympPhi_pullback_ode :
    (HA_a2.subst sympPhi) * (((fun g : PowerSeries ℚ => PBpsi * (PowerSeries.derivative (R := ℚ)) g)^[2]) (HA.subst sympPhi))
      + (HA_a1.subst sympPhi) * ((fun g : PowerSeries ℚ => PBpsi * (PowerSeries.derivative (R := ℚ)) g) (HA.subst sympPhi))
      + (HA_a0.subst sympPhi) * (HA.subst sympPhi) = 0 := by
  -- Eⁱ(H̃) = (DⁱH_A)∘φ (commons iterate_subst_deriv_scaled)
  have hE2 : (((fun g : PowerSeries ℚ => PBpsi * (PowerSeries.derivative (R := ℚ)) g)^[2]) (HA.subst sympPhi)) =
      ((((fun g : PowerSeries ℚ => (PowerSeries.derivative (R := ℚ)) g)^[2]) HA).subst sympPhi) := by
    simpa using (Commons.RingTheory.PowerSeries.iterate_subst_deriv_scaled ℚ HA sympPhi PBpsi 2
      sympPhi_hasSubst sympPhi_deriv_mul_PBpsi)
  have hE1 : ((fun g : PowerSeries ℚ => PBpsi * (PowerSeries.derivative (R := ℚ)) g) (HA.subst sympPhi)) =
      ((((fun g : PowerSeries ℚ => (PowerSeries.derivative (R := ℚ)) g)^[1]) HA).subst sympPhi) := by
    simpa using (Commons.RingTheory.PowerSeries.iterate_subst_deriv_scaled ℚ HA sympPhi PBpsi 1
      sympPhi_hasSubst sympPhi_deriv_mul_PBpsi)
  rw [hE2, hE1]
  -- move the substitutions out: (aᵢ∘φ)·((DⁱHA)∘φ) = (aᵢ·DⁱHA)∘φ
  rw [← PowerSeries.subst_mul sympPhi_hasSubst]
  rw [← PowerSeries.subst_mul sympPhi_hasSubst]
  rw [← PowerSeries.subst_mul sympPhi_hasSubst]
  -- sum of substitutions is the substitution of the sum (the ODE operator applied to HA)
  rw [← PowerSeries.subst_add sympPhi_hasSubst]
  rw [← PowerSeries.subst_add sympPhi_hasSubst]
  -- now the argument equals HA_odeLHS HA = 0
  have hzero : (((fun g : PowerSeries ℚ => (PowerSeries.derivative (R := ℚ)) g)^[2]) HA) = (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) HA) := rfl
  rw [hzero]
  have hone' : (((fun g : PowerSeries ℚ => (PowerSeries.derivative (R := ℚ)) g)^[1]) HA) = (PowerSeries.derivative (R := ℚ)) HA := rfl
  rw [hone']
  rw [← HA_odeLHS_decomp HA]
  rw [HA_ode]
  -- (0).subst φ = 0 (substitution is an algebra homomorphism)
  simpa [PowerSeries.coe_substAlgHom] using (map_zero (PowerSeries.substAlgHom sympPhi_hasSubst))

def PSdd : PowerSeries ℚ → PowerSeries ℚ := fun g => (PowerSeries.derivative (R := ℚ)) g

/-- the formal derivative is additive -/
lemma PSdd_add (a b : PowerSeries ℚ) : PSdd (a + b) = PSdd a + PSdd b := by
  unfold PSdd
  simp

/-- iterated derivatives are additive -/
lemma PSdd_iterate_add (j : ℕ) (a b : PowerSeries ℚ) :
    (PSdd^[j]) (a + b) = (PSdd^[j]) a + (PSdd^[j]) b := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc
        (PSdd^[j + 1]) (a + b) = PSdd ((PSdd^[j]) (a + b)) := by
          rw [Function.iterate_succ_apply']
        _ = PSdd ((PSdd^[j]) a + (PSdd^[j]) b) := by rw [ih]
        _ = PSdd ((PSdd^[j]) a) + PSdd ((PSdd^[j]) b) := PSdd_add _ _
        _ = (PSdd^[j + 1]) a + (PSdd^[j + 1]) b := by
              rw [Function.iterate_succ_apply']
              rw [Function.iterate_succ_apply']

/-- `(r,j)`-entry of the order-4 Wronskian matrix of `u`, `v` against `f`:
rows `u, u′, v, v′`, last row `f`, columns the derivatives `0..4` -/
def wr4Entry (u v f : PowerSeries ℚ) (r j : ℕ) : PowerSeries ℚ :=
  if r = 0 then (PSdd^[j]) u
  else if r = 1 then (PSdd^[j + 1]) u
  else if r = 2 then (PSdd^[j]) v
  else if r = 3 then (PSdd^[j + 1]) v
  else (PSdd^[j]) f

/-- the 5×5 Wronskian matrix -/
def wr4Mat (u v f : PowerSeries ℚ) : Matrix (Fin 5) (Fin 5) (PowerSeries ℚ) :=
  fun r j => wr4Entry u v f r.1 j.1

/-- the order-4 Wronskian operator value `W(u,v)(f) = det(matrix)` -/
def wr4 (u v f : PowerSeries ℚ) : PowerSeries ℚ := (wr4Mat u v f).det

lemma row_eq_left (u v : PowerSeries ℚ) : (wr4Mat u v u) (0 : Fin 5) = (wr4Mat u v u) (4 : Fin 5) := by
  funext j
  unfold wr4Mat wr4Entry
  simp

lemma row_eq_right (u v : PowerSeries ℚ) : (wr4Mat u v v) (2 : Fin 5) = (wr4Mat u v v) (4 : Fin 5) := by
  funext j
  unfold wr4Mat wr4Entry
  simp

lemma row_eq_left_deriv (u v : PowerSeries ℚ) :
    (wr4Mat u v (PSdd u)) (1 : Fin 5) = (wr4Mat u v (PSdd u)) (4 : Fin 5) := by
  funext j
  unfold wr4Mat wr4Entry
  simp

lemma row_eq_right_deriv (u v : PowerSeries ℚ) :
    (wr4Mat u v (PSdd v)) (3 : Fin 5) = (wr4Mat u v (PSdd v)) (4 : Fin 5) := by
  funext j
  unfold wr4Mat wr4Entry
  simp

/-- the Wronskian kills `u` (rows 0 and 4 coincide) -/
lemma wr4_left (u v : PowerSeries ℚ) : wr4 u v u = 0 := by
  unfold wr4
  exact Matrix.det_zero_of_row_eq (M := wr4Mat u v u) (i := (0 : Fin 5)) (j := (4 : Fin 5))
    (by decide) (row_eq_left u v)

/-- the Wronskian kills `v` (rows 2 and 4 coincide) -/
lemma wr4_right (u v : PowerSeries ℚ) : wr4 u v v = 0 := by
  unfold wr4
  exact Matrix.det_zero_of_row_eq (M := wr4Mat u v v) (i := (2 : Fin 5)) (j := (4 : Fin 5))
    (by decide) (row_eq_right u v)

/-- the Wronskian kills `u′` (rows 1 and 4 coincide) -/
lemma wr4_left_deriv (u v : PowerSeries ℚ) : wr4 u v (PSdd u) = 0 := by
  unfold wr4
  exact Matrix.det_zero_of_row_eq (M := wr4Mat u v (PSdd u)) (i := (1 : Fin 5)) (j := (4 : Fin 5))
    (by decide) (row_eq_left_deriv u v)

/-- the Wronskian kills `v′` (rows 3 and 4 coincide) -/
lemma wr4_right_deriv (u v : PowerSeries ℚ) : wr4 u v (PSdd v) = 0 := by
  unfold wr4
  exact Matrix.det_zero_of_row_eq (M := wr4Mat u v (PSdd v)) (i := (3 : Fin 5)) (j := (4 : Fin 5))
    (by decide) (row_eq_right_deriv u v)

/-- the Wronskian kills the sum `u + v` (multilinearity of the last row) -/
lemma wr4_sum (u v : PowerSeries ℚ) : wr4 u v (u + v) = 0 := by
  unfold wr4
  have hsplit : wr4Mat u v (u + v) =
      (wr4Mat u v u).updateRow 4 ((wr4Mat u v u) 0 + (wr4Mat u v u) 2) := by
    ext r j
    fin_cases r
    · simp [wr4Mat, wr4Entry, Matrix.updateRow_apply]
    · simp [wr4Mat, wr4Entry, Matrix.updateRow_apply]
    · simp [wr4Mat, wr4Entry, Matrix.updateRow_apply]
    · simp [wr4Mat, wr4Entry, Matrix.updateRow_apply]
    · simp [wr4Mat, wr4Entry, Matrix.updateRow_apply]
      have hI := PSdd_iterate_add j.1 u v
      rw [hI]
      rw [map_add]
  rw [hsplit]
  rw [Matrix.det_updateRow_add]
  have h1 : ((wr4Mat u v u).updateRow 4 ((wr4Mat u v u) 0)).det = 0 := by
    exact Matrix.det_zero_of_row_eq (M := (wr4Mat u v u).updateRow 4 ((wr4Mat u v u) 0))
      (i := (0 : Fin 5)) (j := (4 : Fin 5)) (by decide) (by
        simp [Matrix.updateRow_apply])
  have h2 : ((wr4Mat u v u).updateRow 4 ((wr4Mat u v u) 2)).det = 0 := by
    exact Matrix.det_zero_of_row_eq (M := (wr4Mat u v u).updateRow 4 ((wr4Mat u v u) 2))
      (i := (2 : Fin 5)) (j := (4 : Fin 5)) (by decide) (by
        simp [Matrix.updateRow_apply])
  rw [h1, h2]
  norm_num

/-- **order-4 `x`-ODE for `F = H_A + H_A∘φ`** (Wronskian form): the operator
built from `u = H_A`, `v = H_A∘φ` and their first derivatives annihilates
the symmetrization input `F`. -/
theorem HAF_wronskian_ode : wr4 HA (HA.subst sympPhi) HAF = 0 := by
  have h := wr4_sum HA (HA.subst sympPhi)
  -- HAF = HA + HA.subst sympPhi by definition
  simpa [HAF] using h
/-- the 4×4 matrix of the leading coefficient: rows `u, u′, v, v′`, columns
the derivatives `0..3` -/
def wr4LeadMat (u v : PowerSeries ℚ) : Matrix (Fin 4) (Fin 4) (PowerSeries ℚ) :=
  fun r j =>
    if r.1 = 0 then (PSdd^[j.1]) u
    else if r.1 = 1 then (PSdd^[j.1 + 1]) u
    else if r.1 = 2 then (PSdd^[j.1]) v
    else (PSdd^[j.1 + 1]) v

/-- the leading coefficient of the order-4 Wronskian operator: the 4×4
Wronskian determinant of `u, u′, v, v′` (the coefficient Laplace expansion
along the `f`-row attaches to `f⁗`) -/
def wr4Lead (u v : PowerSeries ℚ) : PowerSeries ℚ := (wr4LeadMat u v).det

/-- the monic-normalized order-4 operator `M(f) := wr4Lead(u,v)⁻¹·wr4(u,v)(f)`.
When the Laplace expansion `wr4 u v f = wr4Lead u v·f⁗ + Σⱼ₌₀³ sⱼ·f⁽ʲ⁾` is
established, this is the monic order-4 `x`-form of the Wronskian operator
(leading coefficient `1`). -/
def wr4Monic (u v f : PowerSeries ℚ) : PowerSeries ℚ := (wr4Lead u v)⁻¹ * wr4 u v f

/-- the monic Wronskian operator kills `u` -/
lemma wr4Monic_left (u v : PowerSeries ℚ) : wr4Monic u v u = 0 := by
  unfold wr4Monic
  rw [wr4_left]
  simp

/-- the monic Wronskian operator kills `v` -/
lemma wr4Monic_right (u v : PowerSeries ℚ) : wr4Monic u v v = 0 := by
  unfold wr4Monic
  rw [wr4_right]
  simp

/-- the monic Wronskian operator kills `u′` -/
lemma wr4Monic_left_deriv (u v : PowerSeries ℚ) : wr4Monic u v (PSdd u) = 0 := by
  unfold wr4Monic
  rw [wr4_left_deriv]
  simp

/-- the monic Wronskian operator kills `v′` -/
lemma wr4Monic_right_deriv (u v : PowerSeries ℚ) : wr4Monic u v (PSdd v) = 0 := by
  unfold wr4Monic
  rw [wr4_right_deriv]
  simp

/-- the monic Wronskian operator kills the sum `u + v` -/
lemma wr4Monic_sum (u v : PowerSeries ℚ) : wr4Monic u v (u + v) = 0 := by
  unfold wr4Monic
  rw [wr4_sum]
  simp

/-- **monic order-4 `x`-ODE for `F = H_A + H_A∘φ`**: the Wronskian operator
of `u = H_A`, `v = H_A∘φ`, normalized by its leading 4×4 Wronskian, kills
`F`. -/
theorem HAF_wronskian_monic_ode : wr4Monic HA (HA.subst sympPhi) HAF = 0 := by
  have h := wr4Monic_sum HA (HA.subst sympPhi)
  simpa [HAF] using h
/-- row `4` of the Wronskian matrix is the `f`-row -/
lemma wr4Mat_row_four (u v f : PowerSeries ℚ) (j : Fin 5) :
    (wr4Mat u v f) (4 : Fin 5) j = (PSdd^[j.1]) f := by
  unfold wr4Mat wr4Entry
  simp

/-- `wr4Entry` at a row `< 4` does not depend on `f` -/
lemma wr4Entry_of_lt_four (u v f g : PowerSeries ℚ) (a b : ℕ) (ha : a ≤ 3) :
    wr4Entry u v f a b = wr4Entry u v g a b := by
  unfold wr4Entry
  interval_cases a <;> simp

/-- `(4 : Fin 5).succAbove` keeps the value -/
lemma succAbove_four_val (r : Fin 4) : ((4 : Fin 5).succAbove r).1 = r.1 := by
  simpa using (congrArg Fin.val (Fin.succAbove_last_apply r))

/-- deleting the `f`-row (row 4) makes the Wronskian matrix independent of `f` -/
lemma wr4Mat_submatrix_eq (u v f : PowerSeries ℚ) (j : Fin 5) :
    (wr4Mat u v f).submatrix (Fin.succAbove (4 : Fin 5)) (Fin.succAbove j) =
      (wr4Mat u v 0).submatrix (Fin.succAbove (4 : Fin 5)) (Fin.succAbove j) := by
  funext r
  funext c
  rw [Matrix.submatrix_apply, Matrix.submatrix_apply]
  unfold wr4Mat
  rw [wr4Entry_of_lt_four u v f 0 ((4 : Fin 5).succAbove r).1 (((j : Fin 5).succAbove c).1) (by
    rw [succAbove_four_val r]
    omega)]

/-- the signed 4×4 minor of the Wronskian matrix: rows `u,u′,v,v′`, columns
`Fin 5 ∖ {j}` (Laplace cofactor of column `j` for the `f`-row) -/
def wr4Minor (u v : PowerSeries ℚ) (j : Fin 5) : PowerSeries ℚ :=
  ((wr4Mat u v 0).submatrix (Fin.succAbove (4 : Fin 5)) (Fin.succAbove j)).det

/-- the last column's minor is the leading coefficient `wr4Lead` -/
lemma wr4Minor_last (u v : PowerSeries ℚ) : wr4Minor u v (4 : Fin 5) = wr4Lead u v := by
  unfold wr4Minor wr4Lead
  congr 1
  funext r
  funext c
  simp only [Matrix.submatrix_apply]
  unfold wr4Mat wr4LeadMat wr4Entry
  rw [succAbove_four_val r, succAbove_four_val c]
  fin_cases r <;> simp

/-- **Laplace expansion of the Wronskian operator along the `f`-row**:
`wr4 u v f = Σⱼ (−1)^{4+j} · f⁽ʲ⁾ · (4×4 minor of column `j`)` -/
lemma wr4_expand (u v f : PowerSeries ℚ) :
    wr4 u v f = ∑ j : Fin 5, ((-1 : PowerSeries ℚ) ^ ((4 : Fin 5).1 + j.1)) * (PSdd^[j.1]) f * wr4Minor u v j := by
  unfold wr4 wr4Minor
  rw [Matrix.det_succ_row (A := wr4Mat u v f) (i := (4 : Fin 5))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [wr4Mat_row_four]
  rw [wr4Mat_submatrix_eq]


/-- **row-expansion, monic form**: `wr4 u v f = wr4Lead u v·f⁗ + Σₖ₌₀³ sₖ·f⁽ᵏ⁾`
with the signed minors `sₖ = (−1)^{4+k}·wr4Minor u v k` (columns `0..3`) -/
lemma wr4_expand_monic (u v f : PowerSeries ℚ) :
    wr4 u v f = wr4Lead u v * (PSdd^[4]) f
      + ∑ k : Fin 4,
          ((-1 : PowerSeries ℚ) ^ (4 + k.1)) * (wr4Minor u v k.castSucc) * (PSdd^[k.1]) f := by
  rw [wr4_expand]
  -- split the Fin-5 sum into columns 0..3 and the last column 4
  rw [Fin.sum_univ_castSucc (n := 4)]
  -- the last-column term is the leading term
  have htail : ((-1 : PowerSeries ℚ) ^ ((4 : Fin 5).1 + (Fin.last 4).1)) * (PSdd^[(Fin.last 4).1]) f *
        wr4Minor u v (Fin.last 4) = wr4Lead u v * (PSdd^[4]) f := by
    have hlast : (Fin.last 4 : Fin 5) = (4 : Fin 5) := by
      apply Fin.ext
      norm_num
    rw [hlast]
    rw [wr4Minor_last]
    norm_num
    ring
  rw [htail]
  -- the remaining Fin-4 sums agree termwise
  rw [add_comm]
  apply congrArg (fun x => wr4Lead u v * (PSdd^[4]) f + x)
  apply Finset.sum_congr rfl
  intro k hk
  have h4 : (4 : Fin 5).1 = 4 := by norm_num
  rw [h4, Fin.val_castSucc]
  ring
/-- `G_A∘y = F = H_A + H_A∘φ` (the substitution form of `sympSym_subst`) -/
lemma GA_subst_sympY : (sympSym HA).subst sympY = HAF := by
  rw [sympSym_subst, HAF]

/-- **push-down bridge, first order**: the `x`-derivative of
`F = G_A∘y` is `(G_A′∘y)·y′` (chain rule of formal substitution) -/
lemma HAF_deriv_chain :
    (PowerSeries.derivative (R := ℚ)) HAF =
      ((PowerSeries.derivative (R := ℚ)) (sympSym HA)).subst sympY * (PowerSeries.derivative (R := ℚ)) sympY := by
  have h := PowerSeries.derivative_subst (f := sympSym HA) (g := sympY) sympY_hasSubst
  -- h : derivative ((sympSym HA).subst sympY) = (derivative (sympSym HA)).subst sympY * derivative sympY
  rwa [GA_subst_sympY] at h

/-- `y′ = X·(X−2)·(X−1)⁻²` — the closed form of the derivative of the
symmetrization coordinate `y = x²/(x−1)` (so `y′ = X·unit`) -/
lemma sympY_deriv_eq : (PowerSeries.derivative (R := ℚ)) sympY =
    (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2) * (((X : PowerSeries ℚ) - 1)⁻¹) ^ 2 := by
  let W : PowerSeries ℚ := ((X : PowerSeries ℚ) - 1)⁻¹
  have hXW : X * W = 1 + W := by
    have hWX0 : W * X - W = 1 := by
      calc
        W * X - W = W * ((X : PowerSeries ℚ) - 1) := by ring
        _ = 1 := XsubOne_unit_mul
    calc
      X * W = W * X := by ring
      _ = 1 + W := by
            calc
              W * X = (W * X - W) + W := by ring
              _ = 1 + W := by rw [hWX0]
  have hW : (PowerSeries.derivative (R := ℚ)) W = -(W ^ 2) := by
    dsimp [W]
    exact XsubOne_inv_deriv
  have hWX1 : W * X - W = 1 := by
    calc
      W * X - W = W * ((X : PowerSeries ℚ) - 1) := by ring
      _ = 1 := XsubOne_unit_mul
  have h2m : 2 - X * W = W * ((X : PowerSeries ℚ) - 2) := by
    calc
      2 - X * W = 2 - (1 + W) := by rw [hXW]
      _ = 1 - W := by ring
      _ = W * ((X : PowerSeries ℚ) - 2) := by
            calc
              1 - W = (W * X - W) - W := by rw [hWX1]
              _ = W * ((X : PowerSeries ℚ) - 2) := by ring
  have hfin : X * (X * (-(W ^ 2)) + W) + X * W = X * ((X : PowerSeries ℚ) - 2) * W ^ 2 := by
    calc
      X * (X * (-(W ^ 2)) + W) + X * W = X * W * (2 - X * W) := by ring
      _ = X * W * (W * ((X : PowerSeries ℚ) - 2)) := by rw [h2m]
      _ = X * ((X : PowerSeries ℚ) - 2) * W ^ 2 := by ring
  calc
    (PowerSeries.derivative (R := ℚ)) sympY = (PowerSeries.derivative (R := ℚ)) (X * (X * W)) := by
          have hdefY : sympY = X * (X * W) := by
            unfold sympY sympPhi
            rfl
          rw [hdefY]
    _ = X * (PowerSeries.derivative (R := ℚ)) (X * W) + X * W := by
          rw [Derivation.leibniz]
          simp
    _ = X * (X * (PowerSeries.derivative (R := ℚ)) W + W) + X * W := by
          rw [Derivation.leibniz]
          simp
    _ = X * (X * (-(W ^ 2)) + W) + X * W := by rw [hW]
    _ = X * ((X : PowerSeries ℚ) - 2) * W ^ 2 := hfin
    _ = X * ((X : PowerSeries ℚ) - 2) * (((X : PowerSeries ℚ) - 1)⁻¹) ^ 2 := by
          dsimp [W]

/-! ## Faà di Bruno (chain rule, orders 1–4) for `F = G∘y` — route (b), step (1)

The push-down of the order-4 `x`-ODE to the `y`-ODE (paper eq. (explicitode))
first needs the *iterated chain rule*: for `F = G∘y` (any `G ∈ ℚ⟦Y⟧`), the
`x`-derivatives `DⁱF` are expressed as linear combinations of the composed
`y`-derivatives `(DᵏG)∘y` with coefficients polynomial in `y′, y″, …`
(Faà di Bruno to order 4).  `dd_mul` is the product rule in ring form; the
four `d_subst_chain`/`d2_subst_chain`/`d3_subst_chain`/`d4_subst_chain`
lemmas are the identities
`D(G∘y) = (G′∘y)·y′`, `D²(G∘y) = (G″∘y)(y′)² + (G′∘y)·y″`,
`D³(G∘y) = (G‴∘y)(y′)³ + 3(G″∘y)y′y″ + (G′∘y)·y‴`,
`D⁴(G∘y) = (G⁗∘y)(y′)⁴ + 6(G‴∘y)(y′)²y″ + (G″∘y)(4y′y‴+3(y″)²) + (G′∘y)·y⁗`.
With `G := sympSym HA` and `F = HAF = G∘y` (`GA_subst_sympY`) these give
the four `HAF_di_chain` statements — the first ingredient of the
elimination that produces the `y`-ODE.  (The elimination itself needs the
`ℚ(x)`-structure of the solution space `span{H_A, H_A′, H_A∘φ, (H_A∘φ)′}`
of the monic Wronskian `x`-ODE — see the module docstring.)
-/

/-- product rule for the formal derivative, in ring-multiplication form -/
lemma dd_mul (A B : PowerSeries ℚ) :
    (PowerSeries.derivative (R := ℚ)) (A * B) =
      A * (PowerSeries.derivative (R := ℚ)) B + B * (PowerSeries.derivative (R := ℚ)) A := by
  rw [(PowerSeries.derivative (R := ℚ)).leibniz A B]
  simp

/-- chain rule, order 1: `D(G∘y) = (G′∘y)·y′` -/
lemma d_subst_chain (G : PowerSeries ℚ) :
    (PowerSeries.derivative (R := ℚ)) (G.subst sympY) =
      ((PowerSeries.derivative (R := ℚ)) G).subst sympY * (PowerSeries.derivative (R := ℚ)) sympY := by
  simpa using (PowerSeries.derivative_subst (f := G) (g := sympY) sympY_hasSubst)

/-- chain rule, order 2: `D²(G∘y) = (G″∘y)·(y′)² + (G′∘y)·y″` -/
lemma d2_subst_chain (G : PowerSeries ℚ) :
    (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) (G.subst sympY)) =
      ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) G)).subst sympY
          * ((PowerSeries.derivative (R := ℚ)) sympY) ^ 2
        + ((PowerSeries.derivative (R := ℚ)) G).subst sympY
          * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) sympY) := by
  rw [d_subst_chain G, dd_mul]
  rw [d_subst_chain (PowerSeries.derivative (R := ℚ) G)]
  simp [pow_two]
  ring

/-- chain rule, order 3: `D³(G∘y) = (G‴∘y)(y′)³ + 3(G″∘y)y′y″ + (G′∘y)y‴` -/
lemma d3_subst_chain (G : PowerSeries ℚ) :
    (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) (G.subst sympY))) =
      ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) G))).subst sympY
          * ((PowerSeries.derivative (R := ℚ)) sympY) ^ 3
        + 3 * ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) G)).subst sympY
          * ((PowerSeries.derivative (R := ℚ)) sympY) * ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) sympY))
        + ((PowerSeries.derivative (R := ℚ)) G).subst sympY
          * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) sympY)) := by
  rw [d2_subst_chain G]
  rw [map_add]
  rw [(PowerSeries.derivative (R := ℚ)).leibniz _ _]
  rw [(PowerSeries.derivative (R := ℚ)).leibniz _ _]
  rw [d_subst_chain ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) G))]
  rw [pow_two]
  rw [(PowerSeries.derivative (R := ℚ)).leibniz _ _]
  rw [d_subst_chain (PowerSeries.derivative (R := ℚ) G)]
  simp
  ring

/-- chain rule, order 4: `D⁴(G∘y) = (G⁗∘y)(y′)⁴ + 6(G‴∘y)(y′)²y″
+ (G″∘y)(4y′y‴ + 3(y″)²) + (G′∘y)·y⁗` -/
lemma d4_subst_chain (G : PowerSeries ℚ) :
    (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ))
        ((PowerSeries.derivative (R := ℚ)) (G.subst sympY)))) =
      ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ))
        ((PowerSeries.derivative (R := ℚ)) G)))).subst sympY * ((PowerSeries.derivative (R := ℚ)) sympY) ^ 4
      + 6 * (((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) G))).subst sympY)
          * (((PowerSeries.derivative (R := ℚ)) sympY) ^ 2) * ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) sympY))
      + (((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) G)).subst sympY)
          * (4 * ((PowerSeries.derivative (R := ℚ)) sympY) * ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) sympY)))
            + 3 * (((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) sympY)) ^ 2))
      + ((PowerSeries.derivative (R := ℚ)) G).subst sympY
          * ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ))
            ((PowerSeries.derivative (R := ℚ)) sympY)))) := by
  rw [d3_subst_chain G]
  simp only [map_add, dd_mul, derivative_pow]
  simp only [d_subst_chain]
  have h3d : (PowerSeries.derivative (R := ℚ)) (3 : PowerSeries ℚ) = 0 := by
    rw [show (3 : PowerSeries ℚ) = C (3 : ℚ) by rfl]
    simp
  rw [h3d]
  ring

/-- **push-down bridge, orders 2–4** for `F = HAF = G_A∘y` (`G_A := sympSym HA`):
  the `x`-derivatives of `F` expressed through the composed `y`-derivatives of
  `G_A` (the `y′`-monomials of the chain rule) —- the concrete form the monic
  `x`-ODE takes when read in `y`-coordinates. -/
lemma HAF_d2_chain :
    (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) HAF) =
      ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) (sympSym HA))).subst sympY
          * ((PowerSeries.derivative (R := ℚ)) sympY) ^ 2
        + ((PowerSeries.derivative (R := ℚ)) (sympSym HA)).subst sympY
          * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) sympY) := by
  rw [← GA_subst_sympY]
  exact d2_subst_chain (sympSym HA)

lemma HAF_d3_chain :
    (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) HAF)) =
      ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) (sympSym HA)))).subst sympY
          * ((PowerSeries.derivative (R := ℚ)) sympY) ^ 3
        + 3 * ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) (sympSym HA))).subst sympY
          * ((PowerSeries.derivative (R := ℚ)) sympY) * ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) sympY))
        + ((PowerSeries.derivative (R := ℚ)) (sympSym HA)).subst sympY
          * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) sympY)) := by
  rw [← GA_subst_sympY]
  exact d3_subst_chain (sympSym HA)

lemma HAF_d4_chain :
    (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ))
        ((PowerSeries.derivative (R := ℚ)) HAF))) =
      ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ))
        ((PowerSeries.derivative (R := ℚ)) (sympSym HA))))).subst sympY * ((PowerSeries.derivative (R := ℚ)) sympY) ^ 4
      + 6 * (((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) (sympSym HA)))).subst sympY)
          * (((PowerSeries.derivative (R := ℚ)) sympY) ^ 2) * ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) sympY))
      + (((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) (sympSym HA))).subst sympY)
          * (4 * ((PowerSeries.derivative (R := ℚ)) sympY) * ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) sympY)))
            + 3 * (((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) sympY)) ^ 2))
      + ((PowerSeries.derivative (R := ℚ)) (sympSym HA)).subst sympY
          * ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ))
            ((PowerSeries.derivative (R := ℚ)) sympY)))) := by
  rw [← GA_subst_sympY]
  exact d4_subst_chain (sympSym HA)


/-- **expanded order-4 `x`-ODE for `F = HAF`** (no normalization): the
Wronskian expansion `wr4 u v f = wr4Lead·f⁗ + Σ_{k<4} (−1)^{4+k}·minorₖ·f⁽ᵏ⁾`
(`wr4_expand_monic`) kills `F = H_A + H_A∘φ`.  This is the exact form the
order-4 `x`-ODE takes before any division by the leading coefficient
`wr4Lead` (whose constant term is nonzero — the determinant of the
`4×4` Wronskian of `H_A, H_A′, H_A∘φ, (H_A∘φ)′` at `0` equals `37290132`
— so a monic normalization is possible); it is the form the push-down
substitutes the chain rules (`HAF_di_chain`) into. -/
lemma HAF_wronskian_expanded_ode :
    wr4Lead HA (HA.subst sympPhi) * (PSdd^[4]) HAF
      + ∑ k : Fin 4, ((-1 : PowerSeries ℚ) ^ (4 + k.1)) * (wr4Minor HA (HA.subst sympPhi) k.castSucc) * (PSdd^[k.1]) HAF = 0 := by
  have hE := wr4_expand_monic HA (HA.subst sympPhi) HAF
  rw [HAF_wronskian_ode] at hE
  simpa using hE.symm


/-! ## `wr4Lead` is a unit: the constant term `37290132 ≠ 0`

The leading coefficient `wr4Lead u v` (the 4×4 Wronskian determinant of
`u, u′, v, v′`) has a nonzero constant term for `u = H_A`, `v = H_A∘φ`:
`RingHom.map_det` moves `constantCoeff` inside the determinant, the sixteen
per-entry constant terms are `j!·[x^j]u`, `(j+1)!·[x^{j+1}]u`,
`j!·[x^j]v`, `(j+1)!·[x^{j+1}]v` (the generic `cc_iter`, via the commons
`iterate_derivative_coeff_fact`; coefficient values `a₀..a₄ = 1,3,15,93,639`
and `v₀..v₄ = 1,−3,12,−66,402`), and the resulting concrete 4×4
determinant over `ℚ` evaluates to `37290132`
(`wr4LeadConstMat_det`, Laplace along row 0 via `Matrix.det_succ_row_zero`
plus `det_fin_three`).  Hence `wr4Lead HA (HA.subst sympPhi)` is a unit of
`ℚ⟦X⟧` (`wr4Lead_isUnit`), which is what the *monic* normalization
`D⁴F + Σⱼ sⱼ·DʲF = 0`, `sⱼ := (−1)^{4+j}·wr4Lead⁻¹·wr4Minor(u,v,j)`, of
the expanded order-4 `x`-ODE needs.
-/

/-- constant term of the `i`-fold derivative of `t` equals `i!·[x^i]t` -/
lemma cc_iter (t : PowerSeries ℚ) (i : ℕ) :
    PowerSeries.constantCoeff ((PSdd^[i]) t) =
      (Nat.factorial i : ℚ) * PowerSeries.coeff i t := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hP : PSdd = (fun g : PowerSeries ℚ => (PowerSeries.derivative (R := ℚ)) g) := rfl
  rw [hP]
  rw [Commons.RingTheory.PowerSeries.iterate_derivative_coeff_fact]
  congr 1
  · rw [Nat.zero_add, Nat.factorial_zero]
    simp
  · rw [Nat.zero_add]

/-- the concrete 4×4 matrix of the Wronskian constants of
`H_A, H_A′, H_A∘φ, (H_A∘φ)′` at `0` -/
abbrev wr4LeadConstMat : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 3, 30, 558; 3, 30, 558, 15336; 1, -3, 24, -396; -3, 24, -396, 9648]

/-- determinant of the concrete constant matrix -/
lemma wr4LeadConstMat_det : wr4LeadConstMat.det = 37290132 := by
  rw [Matrix.det_succ_row_zero wr4LeadConstMat]
  simp [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove]
  norm_num

/-- **constant term of the leading Wronskian coefficient**:
`wr4Lead(H_A, H_A∘φ)(0) = 37290132` (the 4×4 Wronskian determinant of
`H_A, H_A′, H_A∘φ, (H_A∘φ)′` at `0`). -/
lemma wr4Lead_constantCoeff :
    PowerSeries.constantCoeff (wr4Lead HA (HA.subst sympPhi)) = 37290132 := by
  unfold wr4Lead
  rw [RingHom.map_det (f := (PowerSeries.constantCoeff : PowerSeries ℚ →+* ℚ))
    (M := wr4LeadMat HA (HA.subst sympPhi))]
  have hmat : (PowerSeries.constantCoeff.mapMatrix (wr4LeadMat HA (HA.subst sympPhi))) =
      wr4LeadConstMat := by
    apply Matrix.ext
    intro r j
    fin_cases r <;> fin_cases j
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      simp [wr4LeadMat]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      rw [coeff_HA, HA_coeff_zero]
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      simp [wr4LeadMat]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp only [PSdd, coeff_derivative, coeff_HA]
      norm_num [HA_coeff_one]
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      simp [wr4LeadMat]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp only [PSdd, coeff_derivative, coeff_HA]
      norm_num [HA_coeff_two]
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      simp [wr4LeadMat]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp only [PSdd, coeff_derivative, coeff_HA]
      norm_num [HA_coeff_three]
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      simp [wr4LeadMat]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp only [PSdd, coeff_derivative, coeff_HA]
      norm_num [HA_coeff_one]
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      simp [wr4LeadMat]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp only [PSdd, coeff_derivative, coeff_HA]
      norm_num [HA_coeff_two]
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      simp [wr4LeadMat]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp only [PSdd, coeff_derivative, coeff_HA]
      norm_num [HA_coeff_three]
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      simp [wr4LeadMat]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp only [PSdd, coeff_derivative, coeff_HA]
      norm_num [HA_coeff_four]
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      simp [wr4LeadMat]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      rw [coeff_HA_subst_sympPhi_zero]
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      simp [wr4LeadMat]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp only [PSdd, coeff_derivative]
      norm_num [coeff_HA_subst_sympPhi_one]
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      simp [wr4LeadMat]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp only [PSdd, coeff_derivative]
      norm_num [coeff_HA_subst_sympPhi_two]
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      simp [wr4LeadMat]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp only [PSdd, coeff_derivative]
      norm_num
      rw [coeff_HA_subst_sympPhi_three]
      norm_num
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      simp [wr4LeadMat]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp only [PSdd, coeff_derivative]
      norm_num [coeff_HA_subst_sympPhi_one]
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      simp [wr4LeadMat]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp only [PSdd, coeff_derivative]
      norm_num [coeff_HA_subst_sympPhi_two]
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      simp [wr4LeadMat]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp only [PSdd, coeff_derivative]
      norm_num [coeff_HA_subst_sympPhi_three]
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      simp [wr4LeadMat]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp only [PSdd, coeff_derivative]
      norm_num [coeff_HA_subst_sympPhi_four]
  rw [hmat]
  exact wr4LeadConstMat_det

/-- the leading Wronskian coefficient is a unit of `ℚ⟦X⟧` (nonzero constant
term `37290132`) -/
lemma wr4Lead_isUnit : IsUnit (wr4Lead HA (HA.subst sympPhi)) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  exact isUnit_iff_ne_zero.mpr (by rw [wr4Lead_constantCoeff]; norm_num)

end Submission.CDT
