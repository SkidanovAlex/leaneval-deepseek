/-
  annals_wilkies_conjecture, hole C4a (`C4a_rexp_polyBounded`): sub-hole statements.
  curric-46 C4a design, 2026-10-08. Design text: the C4a report (lead files it next to
  cbc/wilkies_CG_design.md).

  Type-check on 18.221 from the workspace dir (imports the frozen CG and E specs):
    systemd-run --user --scope -q -p MemoryMax=12G -p CPUQuota=200% timeout 1200 \
      lake env lean /abs/path/wilkies_C4a_stmts.lean
  Every `sorry` here is a dispatchable hole. `CurveSel_zero`, `C4a_curve_selection` and
  `C4a_wiring` are PROVED from the holes; `C4a_wiring` has exactly the type of the CG hole
  `C4a_rexp_polyBounded`.

  ROUTE (replaces the square-system + iterated-resultant plan, which fails on excess
  components; see the report):
    per parameter c, analytically, with NO o-minimality:
      rexp slice at x -> oo  ==(C4a_lift)==>  finitely many bounded basic semianalytic pieces
      over t = 1/x with entire data;  analytic CURVE SELECTION in a piece (C4a_curve_selection)
      gives an analytic arc s |-> (t(s), y(s), w(s)) with t(s) > 0;  t(s) = s^N * unit, so
      y = h(t^(1/N)) with h analytic  ==(C4a_asym)==>  y ~ a x^q, q in Q, or eventually 0.
    uniformly in c (C4a_uniform): c |-> lim f_c(2x)/f_c(x) = 2^q(c) is definable (C0 + hR),
      its image is countable, hence finite by hUF.
  Curve selection is proved by induction on the ambient dimension: generic real coordinates +
  real Weierstrass preparation (C4a_RW, adapter over lean-pool LocalComplexGeometry), projection
  of the polynomial sign conditions by Tarski–Seidenberg (C4a_TS1, over E's `SA`, shared with
  E4), and lifting over the projected arc by convergent real Puiseux (C4a_puiseux -> C4a_arcLift).

  Library sources the owners should use (lean-pool is a challenge-declared dependency; its
  modules below are NOT yet built in the workspace and must be built once on the box):
    LeanPool.LocalComplexGeometry.ClassicalComplexWPT.Main   classicalComplexWeierstrassPreparation
    LeanPool.LocalComplexGeometry.WPTBridge.Division         exists_analyticWeierstrassDivision
    LeanPool.LocalComplexGeometry.Analytic.Regularization    exists_regularizing_coordinateEquiv
    LeanPool.Puiseux.AlgClosed                               PuiseuxSeries.isAlgClosed (formal)
    Mathlib: contDiffAt_implicitFunction (n = ω: analytic IFT), OpenPartialHomeomorph
      .hasFPowerSeriesAt_symm (analytic inverse), analyticOrderAt, Polynomial.resultant,
      IsLocalMaxOn.exists_multipliers_of_hasStrictFDerivAt (Lagrange).
-/
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.Wilkies.E.Spec

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace WilkiesDesign.CG.C4a
open WilkiesConjecture WilkiesDesign WilkiesDesign.CG

/-! ## 0. Vocabulary -/

/-- A basic semianalytic set: one equation and finitely many strict inequalities. -/
def BasicSA {n l : ℕ} (F : (Fin n → ℝ) → ℝ) (g : Fin l → (Fin n → ℝ) → ℝ) :
    Set (Fin n → ℝ) :=
  {x | F x = 0 ∧ ∀ j, 0 < g j x}

/-- **Analytic curve selection in `ℝⁿ`.** If `q` is in the closure of a basic semianalytic set
whose data are analytic at `q`, an analytic arc starting at `q` runs inside the set. -/
def CurveSel (n : ℕ) : Prop :=
  ∀ (l : ℕ) (F : (Fin n → ℝ) → ℝ) (g : Fin l → (Fin n → ℝ) → ℝ) (q : Fin n → ℝ),
    AnalyticAt ℝ F q → (∀ j, AnalyticAt ℝ (g j) q) → q ∈ closure (BasicSA F g) →
    ∃ γ : ℝ → (Fin n → ℝ), AnalyticAt ℝ γ 0 ∧ γ 0 = q ∧
      ∃ ε > (0 : ℝ), ∀ s ∈ Set.Ioo (0 : ℝ) ε, γ s ∈ BasicSA F g

/-- The Weierstrass polynomial `z^d + Σ_{i<d} aᵢ(x') zⁱ` at `x = (x', z)` (`z` = last coordinate). -/
def wpoly {n d : ℕ} (a : Fin d → (Fin n → ℝ) → ℝ) (x : Fin (n + 1) → ℝ) : ℝ :=
  x (Fin.last n) ^ d + ∑ i : Fin d, a i (Fin.init x) * x (Fin.last n) ^ (i : ℕ)

/-- A monic polynomial in `z` whose coefficients are functions of a parameter `s`. -/
def mpoly {d : ℕ} (c : Fin d → ℝ → ℝ) (s z : ℝ) : ℝ :=
  z ^ d + ∑ j : Fin d, c j s * z ^ (j : ℕ)

/-- **Real Weierstrass preparation, simultaneous, in generic real linear coordinates.**
Finitely many real-analytic germs at `0 ∈ ℝ^{n+1}` that vanish at `0` and are not identically
zero become, after ONE real linear change of coordinates `L`, unit × Weierstrass polynomial in
the last variable. -/
def RealWeierstrass : Prop :=
  ∀ (n k : ℕ) (h : Fin k → (Fin (n + 1) → ℝ) → ℝ),
    (∀ i, AnalyticAt ℝ (h i) 0) → (∀ i, h i 0 = 0) → (∀ i, ¬ (h i =ᶠ[𝓝 0] fun _ => 0)) →
    ∃ (L : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ)) (d : Fin k → ℕ)
      (a : ∀ i, Fin (d i) → (Fin n → ℝ) → ℝ) (u : Fin k → (Fin (n + 1) → ℝ) → ℝ),
      (∀ i j, AnalyticAt ℝ (a i j) 0 ∧ a i j 0 = 0) ∧
      (∀ i, AnalyticAt ℝ (u i) 0 ∧ u i 0 ≠ 0) ∧
      ∀ᶠ x in 𝓝 0, ∀ i, h i (L x) = u i x * wpoly (a i) x

/-- **Convergent real Puiseux for monic polynomials.** For `P(s,z) = z^d + Σ c_j(s) z^j` with
coefficients analytic at `0`, after the ramification `s = r^N` the real roots for small `r > 0`
are the values of finitely many functions analytic at `0`. -/
def PuiseuxReal : Prop :=
  ∀ (d : ℕ) (c : Fin d → ℝ → ℝ), (∀ j, AnalyticAt ℝ (c j) 0) →
    ∃ (N m : ℕ) (ζ : Fin m → ℝ → ℝ), 0 < N ∧ (∀ i, AnalyticAt ℝ (ζ i) 0) ∧
      ∃ r0 > (0 : ℝ), ∀ r ∈ Set.Ioo (0 : ℝ) r0, ∀ z : ℝ,
        (mpoly c (r ^ N) z = 0 ↔ ∃ i, z = ζ i r)

/-- **Tarski–Seidenberg, one projection** (semialgebraic sets in DNF, E's `SA`). -/
def TS1 : Prop :=
  ∀ (m : ℕ) (X : E.SA (m + 1)), ∃ Y : E.SA m, Y.set = projLast X.set

/-- **Lifting sign conditions over an analytic arc** (curve selection in the `(s,z)`-plane for
data polynomial in `z`): if every small `s > 0` admits a `z` realising the sign vector `σ`, then
an analytic `ζ` realises it along `s = r^N`. -/
def ArcLift : Prop :=
  ∀ (k : ℕ) (d : Fin k → ℕ) (c : ∀ i, Fin (d i) → ℝ → ℝ) (σ : Fin k → SignType),
    (∀ i j, AnalyticAt ℝ (c i j) 0) →
    (∃ s0 > (0 : ℝ), ∀ s ∈ Set.Ioo (0 : ℝ) s0, ∃ z : ℝ,
      ∀ i, SignType.sign (mpoly (c i) s z) = σ i) →
    ∃ (N : ℕ) (ζ : ℝ → ℝ), 0 < N ∧ AnalyticAt ℝ ζ 0 ∧
      ∃ r0 > (0 : ℝ), ∀ r ∈ Set.Ioo (0 : ℝ) r0,
        ∀ i, SignType.sign (mpoly (c i) (r ^ N) (ζ r)) = σ i

/-- A bounded basic semianalytic piece over the `t = 1/x` axis. Coordinate `0` is `t`,
coordinate `1` is `y` (or `1/y` when `inv`), the remaining `m` coordinates are witnesses. -/
structure LiftPiece where
  m : ℕ
  l : ℕ
  F : (Fin (m + 2) → ℝ) → ℝ
  g : Fin l → (Fin (m + 2) → ℝ) → ℝ
  inv : Bool

def LiftPiece.set (P : LiftPiece) : Set (Fin (P.m + 2) → ℝ) := BasicSA P.F P.g

/-- Entire data, bounded, over `t > 0`, and the inverted coordinate never vanishes. -/
def LiftPiece.Good (P : LiftPiece) : Prop :=
  (∀ z, AnalyticAt ℝ P.F z) ∧ (∀ j z, AnalyticAt ℝ (P.g j) z) ∧
    Bornology.IsBounded P.set ∧ (∀ z ∈ P.set, 0 < z 0) ∧
    (P.inv = true → ∀ z ∈ P.set, z 1 ≠ 0)

/-- The piece point `z` represents the value `y`. -/
def LiftPiece.Rep (P : LiftPiece) (z : Fin (P.m + 2) → ℝ) (y : ℝ) : Prop :=
  if P.inv then z 1 * y = 1 else z 1 = y

/-- The slice of `Y` at parameter `c`, over `x = 1/t > 1`, is a finite union of projections of
good pieces. -/
def SliceLift {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) : Prop :=
  ∃ L : List LiftPiece, (∀ P ∈ L, P.Good) ∧
    ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ y : ℝ,
      (Fin.cons t⁻¹ (Fin.cons y c) ∈ Y ↔ ∃ P ∈ L, ∃ z ∈ P.set, z 0 = t ∧ P.Rep z y)

/-- Polynomial boundedness with a rational exponent for ONE parameter value. -/
def PBOne {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) : Prop :=
  (∃ R : ℝ, ∀ x y : ℝ, R ≤ x → Fin.cons x (Fin.cons y c) ∈ Y → y = 0) ∨
  ∃ q : ℚ, ∃ a : ℝ, a ≠ 0 ∧ ∀ ε > (0 : ℝ), ∃ R : ℝ, ∀ x y : ℝ, R ≤ x →
    Fin.cons x (Fin.cons y c) ∈ Y → |y / x ^ (q : ℝ) - a| < ε

/-! ## 1. Holes -/

/-- **C4a.RW (adapter, semi-mechanical, 5–10K).** Real-analytic germs complexify (same power
series); a real direction `v` with `hₖ(v) ≠ 0` for the lowest homogeneous part of `∏ hᵢ` makes
every `hᵢ` regular; apply lean-pool `classicalComplexWeierstrassPreparation`; uniqueness +
complex conjugation make `a`, `u` real on real points. -/
theorem C4a_RW : RealWeierstrass := by
  sorry

/-- **C4a.P (research-ish, 8–15K).** Reduce to the square-free part over `Frac ℝ{s}`
(discriminant `≢ 0`); lean-pool `PuiseuxSeries.isAlgClosed` gives `d` distinct formal roots in
`ℂ⟦s^{1/N}⟧` (integral over `ℂ⟦s⟧`, so no negative exponents); each is a SIMPLE root, hence
convergent (Tougeron: with `e = ord P_z(φ)`, put `z = φ_{≤2e} + σ^{e+1} w`, divide by
`σ^{2e+1}`, analytic IFT in `w`, formal uniqueness); real roots for `r > 0` are exactly the
branches with real coefficients. -/
theorem C4a_puiseux : PuiseuxReal := by
  sorry

/-- **C4a.TS (textbook, 10–20K; SHARED with E4, whose CAD needs it).** Cohen–Hörmander:
the sign table of a derivative-closed family of polynomials in `z` is determined by sign
conditions on polynomials in the coefficients. -/
theorem C4a_TS1 : TS1 := by
  sorry

/-- **C4a.AL (mechanical given Puiseux, 4–8K).** Apply `PuiseuxReal` to `∏ Pᵢ`; distinct
branches are eventually strictly ordered (their difference is analytic `≢ 0`); the cells are
the branches, the midpoints of consecutive branches, and `min − 1`, `max + 1`; every `Pᵢ`
evaluated at a cell representative is analytic in `r`, so its sign is eventually constant;
some cell carries `σ` for all small `r`. -/
theorem C4a_arcLift (hP : PuiseuxReal) : ArcLift := by
  sorry

/-- **C4a.CS (research glue, 8–15K).** `CurveSel n → CurveSel (n+1)`. Translate `q = 0`; drop
`gⱼ` with `gⱼ(0) ≠ 0`.
* `n+1 = 1`: signs of analytic `gⱼ` are constant on `(0,ε)` and on `(-ε,0)`.
* `n+1 ≥ 2`, `F ≡ 0` near `0`: replace `F` by `Σ_{a<b}(x_a ∂_bψ − x_b ∂_aψ)²`, where
  `ψ = (1+⟨c,x⟩)∏gⱼ` and `c` is chosen so that this sum is not `≡ 0`. The maximiser of `ψ`
  on `{‖x‖=r, g ≥ 0}` lies in `Y` and satisfies Lagrange, so `0` stays in the closure.
* `RealWeierstrass` on `{F, gⱼ}`. `Y` becomes
  `{P_F = 0, σⱼ·Pⱼ > 0}`, where `σⱼ = sign uⱼ(0)`.
* `TS1` on the SA set in `(coefficients, z)`. The projection near `0` is
  `A⁻¹(Y_alg)`, because real roots of `P_F` are small by the Cauchy bound.
* `0` lies in the closure of one DNF disjunct. Apply `CurveSel n` to get `γ'`.
* `ArcLift` over `γ'` gives `ζ`, and `ζ(0) = 0` since it is a root of `P_F`.
* Output `γ(r) = L(γ'(r^N), ζ(r))`. -/
theorem C4a_CS_step (hW : RealWeierstrass) (hA : ArcLift) (hT : TS1) (n : ℕ)
    (ih : CurveSel n) : CurveSel (n + 1) := by
  sorry

/-- **C4a.L (mechanical, 3–6K).** For `x = 1/t > 1`, `rexp x = 0`. Split every other variable
into `|·|<1` (rexp = exp), `= ±1` (constant), `|·|>1` (rexp = 0; invert `v = 1/w`, condition
`0 < v² < 1`). Clear denominators by `t^D·∏v^D`. Inequalities: `0 < t < 1`, `1 − z² > 0`,
`v² > 0`. -/
theorem C4a_lift {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (hY : RExpExist Y) (c : Fin k → ℝ) :
    SliceLift Y c := by
  sorry

/-- **C4a.A (mechanical analytic, 4–8K).** If the slice domain is bounded, the first disjunct
holds vacuously. Otherwise `tₖ → 0` in one piece, so there is a closure point `q` with `q 0 = 0`
(boundedness). `CurveSel` gives an arc whose `t(s) = s^N·(b + O(s))` with `b > 0`. Invert
`s ↦ s·(t/s^N)^{1/N}` analytically: `y(x) = h(x^{-1/N})` with `h` analytic (or `1/h` for an
inverted piece). Then `h ≡ 0` gives the first disjunct; otherwise `h = a r^k (1+O(r))` gives
`q = ∓k/N`. -/
theorem C4a_asym (hCS : ∀ n, CurveSel n) {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ)
    (hfun : ∀ x y y' : ℝ, Fin.cons x (Fin.cons y c) ∈ Y → Fin.cons x (Fin.cons y' c) ∈ Y →
      y = y')
    (hL : SliceLift Y c) : PBOne Y c := by
  sorry

/-- **C4a.U (o-minimal bookkeeping, 4–8K; uses `C0_rexp_syntax`).** `C₀ = {c : eventually 0}`
and `Λ = {λ : ∃ c ∉ C₀, f_c(2x)/f_c(x) → λ}` are `LRc`-definable, hence `RExpExist` (C0 + hR).
`Λ = {2^{q(c)}}` is countable. `hUF` with `k = 0` makes `Λ` a finite union of preconnected
sets, which are singletons. Take `Qs = {q : 2^q ∈ Λ}`. -/
theorem C4a_uniform
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (hUF : UnifFiniteRExp)
    (h1 : ∀ (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)), RExpExist Y →
      (∀ (c : Fin k → ℝ) (x y y' : ℝ), Fin.cons x (Fin.cons y c) ∈ Y →
        Fin.cons x (Fin.cons y' c) ∈ Y → y = y') →
      ∀ c : Fin k → ℝ, PBOne Y c) :
    PolyBoundedRExp := by
  sorry

/-! ## 2. Wiring (PROVED from the holes) -/

/-- Curve selection in dimension `0` (a one-point space). -/
theorem CurveSel_zero : CurveSel 0 := by
  intro l F g q _ _ hq
  have hne : (BasicSA F g).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hq
    exact hq
  obtain ⟨x, hx⟩ := hne
  have hxq : x = q := Subsingleton.elim x q
  subst hxq
  exact ⟨fun _ => x, analyticAt_const, rfl, 1, one_pos, fun _ _ => hx⟩

/-- Curve selection in every dimension. -/
theorem C4a_curve_selection : ∀ n, CurveSel n := by
  intro n
  induction n with
  | zero => exact CurveSel_zero
  | succ n ih => exact C4a_CS_step C4a_RW (C4a_arcLift C4a_puiseux) C4a_TS1 n ih

/-- **The CG hole `C4a_rexp_polyBounded`, derived from the sub-holes.** -/
theorem C4a_wiring
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (hUF : UnifFiniteRExp) : PolyBoundedRExp :=
  C4a_uniform hR hUF fun _ Y hY hfun c =>
    C4a_asym C4a_curve_selection Y c (hfun c) (C4a_lift Y hY c)

/-- Type check: `C4a_wiring` has exactly the statement of `CG.C4a_rexp_polyBounded`. -/
example : (∀ (_hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (_hUF : UnifFiniteRExp), PolyBoundedRExp) :=
  @C4a_wiring

/-- The CG statement and ours are the same proposition. -/
example : (∀ (_hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (_hUF : UnifFiniteRExp), PolyBoundedRExp) :=
  @WilkiesDesign.CG.C4a_rexp_polyBounded

end WilkiesDesign.CG.C4a
