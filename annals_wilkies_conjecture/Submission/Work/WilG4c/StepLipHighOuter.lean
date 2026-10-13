/-
  WilG4c / StepLipHighOuter — the *outer* assembly of `Work.WilkG4c.StepLipHigh` (BNZ §5.3,
  the `r ≥ 1` slice of the reduction `PY ⟶ PYLip`).

  `Work.WilkG4c.StepLipHighPsi` is the per-chart step: for one chart `ψ` of the `n`-dimensional
  F-lemma applied to the pinned family, and with global `ψ`-data, it produces the charts of `F`
  on a parameter set `Λ` and an `ε`-cover.  This file supplies the *outer* half of
  `StepLipHigh`:

  * the `Λ`-uniformity fix ("globalise first").  `StepLipHighPsi` needs the `ψ`-data for
    **every** parameter, while `YbCharts` only delivers it on `Λ`, and an arbitrary `Λ` is not
    available as an `Ω`-bounded patch set for the clamping devices.  The fix used here is to
    clamp in the **parameter** direction: for each family member `f = F i` let

      `Sᵢ = {l | ∀ w ∈ openCube (n+1), f l w ∈ (0,1)}   (Work.WilkG4c.valSet f)`

    (an `Ω`-bounded set with *additive* format/degree, `Work.WilG4c.valSetMemG`), and put
    `F̃ i l t = if l ∈ Sᵢ then F i l t else 1/2`.  Then

    - `famGraph (F̃ i) ∈ S.Ω` with additive format/degree (`IteFamGraphMem`),
    - `ValuesIn01 univ F̃`, so `YbCharts` may be run with the parameter set `univ` and its
      output `ψ`-data is global,
    - `PY p n r k F̃` — *immediate*, because `YBound` is a per-parameter statement and every
      fibre of `F̃` is either a fibre of `F` or the constant `1/2` (`PY_paramClamp`),
    - `F̃ = F` on `Λ × openCube (n+1)` (by `ValuesIn01 Λ F`), so the resulting charts and
      covers transfer back to `F`.

  * the finite union over the chart family `Ξ` of `YbCharts`, the cardinality arithmetic, and the
    strong induction on `p` (`StepLipHighPsi` takes the induction hypothesis for `q < p` as an
    explicit argument, so no `DescentP` is needed).

  The per-chart step is taken as an explicit *hypothesis* (`PsiHyp` below), so that this file is
  `sorry`-free and becomes usable as soon as that lemma lands.  **`PsiHyp` is the corrected
  interface of `Work.WilkG4c.StepLipHighPsi`**: the cover hypothesis `hψcov` (quantified over
  `∀ y ∈ openCube n` for the fixed chart `ψ`) is dropped and the corresponding condition on the
  target is moved into the conclusion.  See the docstring of `PsiHyp` and the notes in
  `StepLipHighOuter_NOTES.md` for why the interface of `StepLipHighPsi` cannot be satisfied in
  this assembly. -/
import Mathlib
import Submission.Work.WilG4c.StepLipDefs
import Submission.Work.WilG4c.StepLipAux
import Submission.Work.WilG4c.YbCharts
import Submission.Work.WilG4c.IteFamGraphMem
import Submission.Work.WilG4c.valSetMemG
import Submission.Work.WilG4c.PolySubstFirst
import Submission.Work.WilG4a.F1AffineW
import Submission.Work.WilG4c.DescentP

set_option autoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG4c

/-! ## 0. Elementary helpers -/

/-- The open cube is open. -/
theorem isOpen_openCube (μ : ℕ) : IsOpen (openCube μ) := by
  have h : openCube μ = ⋂ i : Fin μ, {t : Fin μ → ℝ | t i ∈ Set.Ioo (0 : ℝ) 1} := by
    ext t; simp [openCube]
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (continuous_apply i)

/-- The set of parameters at which a family member is cube-valued in `(0,1)`; it is the patch
set of the parameter-clamping construction.  Its `Ω`-membership (with additive format and
degree) is `Work.WilG4c.valSetMemG`. -/
def valSet {p M : ℕ} (f : (Fin p → ℝ) → (Fin M → ℝ) → ℝ) : Set (Fin p → ℝ) :=
  {l | ∀ w ∈ openCube M, f l w ∈ Set.Ioo (0 : ℝ) 1}

/-- Clamping a family in the **parameter** direction: on the patch set the member is unchanged,
outside it the member is the constant `c`. -/
def paramClamp {p M : ℕ} (Λs : Set (Fin p → ℝ)) (c : ℝ)
    (f : (Fin p → ℝ) → (Fin M → ℝ) → ℝ) : (Fin p → ℝ) → (Fin M → ℝ) → ℝ :=
  fun l t => if l ∈ Λs then f l t else c

/-- `YBound` is a *per-parameter* statement, so clamping in the parameter direction preserves
it: every fibre of the clamped family is either the original fibre or the constant. -/
theorem PY_paramClamp {p n k : ℕ} (Λs : Fin k → Set (Fin p → ℝ)) (c : ℝ)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (r : ℕ) (F : Family k p (n + 1)) (hPY : PY p n r k F) :
    PY p n r k (fun i => paramClamp (Λs i) c (F i)) := by
  intro i l x hx m hm y hy
  by_cases hl : l ∈ Λs i
  · have hfl : paramClamp (Λs i) c (F i) l = F i l := by
      funext t; simp [paramClamp, hl]
    show ‖iteratedFDeriv ℝ m (slice (paramClamp (Λs i) c (F i) l) x) y‖ ≤ 1
    rw [hfl]
    exact hPY i l x hx m hm y hy
  · have hfl : paramClamp (Λs i) c (F i) l = fun _ => c := by
      funext t; simp [paramClamp, hl]
    show ‖iteratedFDeriv ℝ m (slice (paramClamp (Λs i) c (F i) l) x) y‖ ≤ 1
    rw [hfl]
    have hsl : slice (fun _ : Fin (n + 1) → ℝ => c) x = fun _ : Fin n → ℝ => c := by
      funext y'; simp [slice_apply]
    rw [hsl]
    cases m with
    | zero =>
        rw [norm_iteratedFDeriv_zero]
        show ‖c‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_pos hc.1]
        exact le_of_lt hc.2
    | succ m' => rw [iteratedFDeriv_succ_const]; simp

/-- `ChartsOK` transports across two families that agree on `Λ × openCube n`. -/
theorem ChartsOK_congr {S : SOMin} {p n k a Dg r : ℕ} {Λ : Set (Fin p → ℝ)}
    {F G : Family k p n} {Φ : Finset (ChartTuple p n)}
    (hFG : ∀ i l t, l ∈ Λ → t ∈ openCube n → F i l t = G i l t)
    (h : ChartsOK S a Dg r Λ G Φ) : ChartsOK S a Dg r Λ F Φ := by
  intro φ hφ
  obtain ⟨hmem, hrest⟩ := h φ hφ
  refine ⟨hmem, ?_⟩
  intro l hl
  obtain ⟨hcub, hrest2⟩ := hrest l hl
  refine ⟨hcub, ?_⟩
  intro i
  refine ⟨?_, ?_⟩
  · exact (hrest2 i).1.congr (fun t ht => hFG i l _ hl (hcub t ht))
  · intro m hm' t ht
    have h1 : iteratedFDeriv ℝ m (fun t => F i l (fun j => φ j l t)) t
        = iteratedFDerivWithin ℝ m (fun t => F i l (fun j => φ j l t)) (openCube n) t :=
      (iteratedFDerivWithin_of_isOpen m (isOpen_openCube n) ht).symm
    have h2 : iteratedFDerivWithin ℝ m (fun t => F i l (fun j => φ j l t)) (openCube n) t
        = iteratedFDerivWithin ℝ m (fun t => G i l (fun j => φ j l t)) (openCube n) t :=
      iteratedFDerivWithin_congr (s := openCube n)
        (f₁ := fun t => F i l (fun j => φ j l t))
        (f := fun t => G i l (fun j => φ j l t)) (fun t' ht' => hFG i l _ hl (hcub t' ht')) ht m
    have h3 : iteratedFDerivWithin ℝ m (fun t => G i l (fun j => φ j l t)) (openCube n) t
        = iteratedFDeriv ℝ m (fun t => G i l (fun j => φ j l t)) t :=
      iteratedFDerivWithin_of_isOpen m (isOpen_openCube n) ht
    calc ‖iteratedFDeriv ℝ m (fun t => F i l (fun j => φ j l t)) t‖
        = ‖iteratedFDeriv ℝ m (fun t => G i l (fun j => φ j l t)) t‖ := by rw [h1, h2, h3]
      _ ≤ 1 := (hrest2 i).2 m hm' t ht

/-- `Covers` transports across two families that agree on `Λ × openCube n`; the charts have to
map into the cube for the equality to apply to the chart points (this is what `ChartsOK`
supplies). -/
theorem Covers_congr {p n k : ℕ} {Λ : Set (Fin p → ℝ)} {F G : Family k p n}
    {Φ : Finset (ChartTuple p n)} {ε : ℝ}
    (hcub : ∀ φ ∈ Φ, ∀ l ∈ Λ, ∀ t ∈ openCube n, (fun j => φ j l t) ∈ openCube n)
    (hFG : ∀ i l t, l ∈ Λ → t ∈ openCube n → F i l t = G i l t)
    (h : Covers Λ G Φ ε) : Covers Λ F Φ ε := by
  intro l hl x hx
  obtain ⟨φ, hφ, t, ht, hlt⟩ := h l hl x hx
  refine ⟨φ, hφ, t, ht, fun i => ?_⟩
  rw [hFG i l _ hl (hcub φ hφ l hl t ht), hFG i l _ hl hx]
  exact hlt i

/-- Substituting `X₀ ↦ q` (a polynomial in `(X₀,X₁)`) and `X₃ ↦ X₃ + d` into a real polynomial
in four variables. -/
theorem PolyShift4 (q : MvPolynomial (Fin 2) ℕ) (d : ℝ) (c : MvPolynomial (Fin 4) ℝ) :
    ∃ c' : MvPolynomial (Fin 4) ℝ, ∀ (D r k : ℕ) (u : ℝ),
      MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), u] c' =
        MvPolynomial.eval ![((MvPolynomial.eval ![D, r] q : ℕ) : ℝ), (r : ℝ), (k : ℝ),
          u + d] c := by
  set e : Fin 2 → Fin 4 := fun i => Fin.castLE (by norm_num : 2 ≤ 4) i with he
  set qℝ : MvPolynomial (Fin 4) ℝ :=
    MvPolynomial.rename e (MvPolynomial.map (Nat.castRingHom ℝ) q) with hqdef
  have hqev : ∀ (D r k : ℕ) (u : ℝ),
      MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), u] qℝ
        = ((MvPolynomial.eval ![D, r] q : ℕ) : ℝ) := by
    intro D r k u
    have hcomp : (![(D : ℝ), (r : ℝ), (k : ℝ), u] ∘ e) = ![(D : ℝ), (r : ℝ)] := by
      funext i; fin_cases i <;> simp [he, Fin.castLE]
    rw [hqdef, MvPolynomial.eval_rename, hcomp, MvPolynomial.eval_map]
    have hpt : ![(D : ℝ), (r : ℝ)] = ⇑(Nat.castRingHom ℝ) ∘ ![D, r] := by
      funext i; fin_cases i <;> simp
    rw [hpt]
    exact (MvPolynomial.eval₂_comp (Nat.castRingHom ℝ) ![D, r] q).symm
  set φ : Fin 4 → MvPolynomial (Fin 4) ℝ :=
    ![qℝ, MvPolynomial.X (1 : Fin 4), MvPolynomial.X (2 : Fin 4),
      MvPolynomial.X (3 : Fin 4) + MvPolynomial.C d] with hφ
  refine ⟨MvPolynomial.bind₁ φ c, ?_⟩
  intro D r k u
  have hfun : (fun i : Fin 4 => MvPolynomial.eval₂Hom (RingHom.id ℝ)
      ![(D : ℝ), (r : ℝ), (k : ℝ), u] (φ i))
      = ![((MvPolynomial.eval ![D, r] q : ℕ) : ℝ), (r : ℝ), (k : ℝ), u + d] := by
    funext i
    fin_cases i
    · exact hqev D r k u
    · simp [hφ]
    · simp [hφ]
    · simp [hφ]
  change MvPolynomial.eval₂Hom (RingHom.id ℝ) ![(D : ℝ), (r : ℝ), (k : ℝ), u]
      (MvPolynomial.bind₁ φ c)
    = MvPolynomial.eval₂Hom (RingHom.id ℝ)
        ![((MvPolynomial.eval ![D, r] q : ℕ) : ℝ), (r : ℝ), (k : ℝ), u + d] c
  rw [MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℝ) ![(D : ℝ), (r : ℝ), (k : ℝ), u] φ c, hfun]


/-- The type of the per-chart step at parameter dimension `q`.

**Interface note (important).**  In `Work.WilkG4c.StepLipHighPsi` the cover hypothesis
`hψcov` is stated with the quantifier `∀ y ∈ openCube n` for the *fixed* chart `ψ`, and the
conclusion is the full `Covers Λ F Φ ε`.  Both are stronger than the argument needs and, more
importantly, the hypothesis *cannot be supplied* in the outer assembly: `YbCharts` delivers its
`ε/2`-cover only in the form `∀ l x y, ∃ ψ ∈ Ξ, …`, so a single `ψ` of the family covers only
the part of each fibre that it is responsible for (a chart of the `n`-dimensional F-lemma is a
parametrisation of one cell, and the cell decomposition covers the cube only in the union).

Every consumer (`Work.WilG4c.GoodCellCoverL`, `GoodCellChartsG`, …) uses `hψcov` only at the
*one* fibre point that is being covered (see `GoodCellCoverL`: `hψcov l hl (x 0) hx0I
(Fin.tail x) hxt`).  The correct interface therefore makes that point a *condition on the
target*: the hypothesis `hψcov` disappears and the cover in the conclusion is conditional on
the target being `ψ`-approximable.  The same proof gives the corrected statement, and the
union over the family `Ξ` of `YbCharts` then produces the unconditional cover of `F`. -/
abbrev PsiHyp (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (n q : ℕ) (hn : 1 ≤ n)
    (h1 : ∀ q, Work.WilG4a.F1AffineW S q) (ih : ∀ q, FLem S q n) (hchoice : ChoiceHyp S) (hbdd : BddDxHyp S)
    (hP1q : FLemP S q (n + 1) (PYLip q n))
    (hind : ∀ m, m < q → FLemPHigh S m (n + 1) (PY m n)) : Prop :=
  ∀ (aψ : ℕ) (bψ : MvPolynomial (Fin 2) ℕ) (F0 : ℕ),
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
    ∀ (D r k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hr : 1 ≤ r)
      (Λ : Set (Fin q → ℝ)) (F : Family k q (n + 1))
      (hΩg : ∀ i, famGraph (F i) ∈ S.Ω F0 D (q + (n + 1) + 1))
      (hPY : PY q n r k F)
      (hval : ValuesIn01 Λ F)
      (ψ : ChartTuple (q + 1) n)
      (hψg : ∀ j, famGraph (ψ j) ∈
        S.Ω aψ (MvPolynomial.eval ![D, r] bψ) ((q + 1) + n + 1))
      (hψcube : ∀ l, ∀ x ∈ I, ∀ t ∈ openCube n,
        (fun j => ψ j (Fin.snoc l x) t) ∈ openCube n)
      (hψsm : ∀ i, ∀ l, ∀ x ∈ I,
        ContDiffOn ℝ r (fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)))
          (openCube n))
      (hψnm : ∀ i, ∀ l, ∀ x ∈ I, ∀ m, m ≤ r →
        ∀ t ∈ openCube n,
          ‖iteratedFDeriv ℝ m (fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t))) t‖ ≤ 1),
      ∃ Φ : Finset (ChartTuple q (n + 1)),
        (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
        ChartsOK S a (MvPolynomial.eval ![D, r] b) r Λ F Φ ∧
        (∀ l ∈ Λ, ∀ x ∈ I, ∀ y ∈ openCube n,
          (∃ t ∈ openCube n, ∀ i,
            |F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)) - F i l (Fin.cons x y)|
              < ε / 2) →
          ∃ t ∈ openCube (n + 1), ∃ φ ∈ Φ, ∀ i,
            |F i l (fun j => φ j l t) - F i l (Fin.cons x y)| < ε)

/-! ## 1. The outer assembly -/


/-- **One level of the outer assembly.**  Given the per-chart step `StepLipHighPsi` at the
parameter dimension `q` (together with the induction hypothesis at smaller dimensions, which
`StepLipHighPsi` takes as an argument), the `r ≥ 1` slice at `q` follows: clamp the family in the
parameter direction, run `YbCharts` with the parameter set `univ`, run `StepLipHighPsi` for every
chart `ψ` of the resulting family `Ξ`, take the union, and transfer back to `(Λ, F)`. -/
theorem FLemPHigh_at (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (n q : ℕ) (hn : 1 ≤ n) (h1 : ∀ q, Work.WilG4a.F1AffineW S q) (ih : ∀ q, FLem S q n)
    (hchoice : ChoiceHyp S) (hbdd : BddDxHyp S)
    (hP1q : FLemP S q (n + 1) (PYLip q n))
    (hind : ∀ m, m < q → FLemPHigh S m (n + 1) (PY m n))
    (hPsiHere : PsiHyp S hcd hder n q hn h1 ih hchoice hbdd hP1q hind) :
    FLemPHigh S q (n + 1) (PY q n) := by
  intro F0
  obtain ⟨a_v, c_v, hVal⟩ := Work.WilG4c.valSetMemG S q (n + 1)
  set F0'' : ℕ := F0 + (F0 + a_v) + 3 * (q + (n + 1) + 1) + 3 * q + 6 with hF0''
  set qK : MvPolynomial (Fin 2) ℕ := 3 * MvPolynomial.X 0 + MvPolynomial.C (2 * c_v + 5)
    with hqK
  obtain ⟨aY, bY, cY, HYb⟩ := YbCharts S n q ih F0''
  obtain ⟨aH, bH, cH, HH⟩ := hPsiHere aY bY F0''
  obtain ⟨bH', hbH'⟩ := PolySubstFirst qK bH
  obtain ⟨cY', hcY'⟩ := PolyShift4 qK (Real.log 2) cY
  obtain ⟨cH', hcH'⟩ := PolyShift4 qK 0 cH
  refine ⟨aH, bH', cY' * (cH' * cH' + MvPolynomial.C (1 : ℝ)), ?_⟩
  intro D r k ε hε hε1 hr Λ F hPY hΩg hval
  have hqKval : MvPolynomial.eval ![D, r] qK = 3 * D + (2 * c_v + 5) := by
    rw [hqK]
    simp [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X]
  set D'' : ℕ := 3 * D + (2 * c_v + 5) with hD''
  have hD''q : D'' = MvPolynomial.eval ![D, r] qK := by rw [hD'', hqKval]
  -- the patch sets and the clamped family
  set Λs : Fin k → Set (Fin q → ℝ) := fun i => valSet (F i) with hΛs
  have hΛsmem : ∀ i, Λs i ∈ S.Ω (F0 + a_v) (D + c_v) q := by
    intro i
    have h := hVal F0 D (F i) (hΩg i)
    rw [hΛs]
    exact h
  set Fc : Family k q (n + 1) := fun i => paramClamp (Λs i) (1 / 2 : ℝ) (F i) with hFc
  have hΩFc : ∀ i, famGraph (Fc i) ∈ S.Ω F0'' D'' (q + (n + 1) + 1) := by
    intro i
    have h := IteFamGraphMem S (Λs i) (1 / 2 : ℝ) F Fc i (F0 + a_v) (D + c_v) F0 D
      (hΛsmem i) (hΩg i)
      (fun l t hl => by simp [hFc, paramClamp, hl])
      (fun l t hl => by simp [hFc, paramClamp, hl])
    have h1 : F0 + (F0 + a_v) + 3 * (q + (n + 1) + 1) + 3 * q + 6 = F0'' := by rw [hF0'']
    have h2 : D + 2 * (D + c_v) + 5 = D'' := by rw [hD'']; ring
    rw [h1, h2] at h
    exact h
  have hPYc : PY q n r k Fc := by
    rw [hFc]
    exact PY_paramClamp Λs (1 / 2 : ℝ) (by norm_num) r F hPY
  have hvalc : ValuesIn01 (Set.univ : Set (Fin q → ℝ)) Fc := by
    intro i l _ x hx
    rw [hFc]
    simp only [paramClamp]
    by_cases hl : l ∈ Λs i
    · rw [if_pos hl]
      rw [hΛs] at hl
      exact hl x hx
    · rw [if_neg hl]; norm_num
  obtain ⟨Ξ, hΞcard, hΞok, hΞcov⟩ := HYb D'' r k ε hε hε1 Set.univ Fc hΩFc hvalc
  -- the per-chart step
  have hper : ∀ ψ ∈ Ξ, ∃ Φψ : Finset (ChartTuple q (n + 1)),
      (Φψ.card : ℝ) ≤ MvPolynomial.eval ![(D'' : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cH ∧
      ChartsOK S aH (MvPolynomial.eval ![D'', r] bH) r Set.univ Fc Φψ ∧
      (∀ l ∈ (Set.univ : Set (Fin q → ℝ)), ∀ x ∈ I, ∀ y ∈ openCube n,
        (∃ t ∈ openCube n, ∀ i,
          |Fc i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)) - Fc i l (Fin.cons x y)|
            < ε / 2) →
        ∃ t ∈ openCube (n + 1), ∃ φ ∈ Φψ, ∀ i,
          |Fc i l (fun j => φ j l t) - Fc i l (Fin.cons x y)| < ε) := by
    intro ψ hψ
    obtain ⟨hψg, hψcube, hψsm, hψnm⟩ := hΞok ψ hψ
    exact HH D'' r k ε hε hε1 hr Set.univ Fc hΩFc hPYc hvalc ψ hψg
      (fun l x hx t ht => hψcube l trivial x hx t ht)
      (fun i l x hx => hψsm i l trivial x hx)
      (fun i l x hx m hm t ht => hψnm i l trivial x hx m hm t ht)
  let Φf : ChartTuple (q + 1) n → Finset (ChartTuple q (n + 1)) :=
    fun ψ => if h : ψ ∈ Ξ then (hper ψ h).choose else ∅
  have hΦprops : ∀ (ψ : ChartTuple (q + 1) n) (hψ : ψ ∈ Ξ),
      ((Φf ψ).card : ℝ) ≤ MvPolynomial.eval ![(D'' : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cH ∧
      ChartsOK S aH (MvPolynomial.eval ![D'', r] bH) r Set.univ Fc (Φf ψ) ∧
      (∀ l ∈ (Set.univ : Set (Fin q → ℝ)), ∀ x ∈ I, ∀ y ∈ openCube n,
        (∃ t ∈ openCube n, ∀ i,
          |Fc i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)) - Fc i l (Fin.cons x y)|
            < ε / 2) →
        ∃ t ∈ openCube (n + 1), ∃ φ ∈ Φf ψ, ∀ i,
          |Fc i l (fun j => φ j l t) - Fc i l (Fin.cons x y)| < ε) := by
    intro ψ hψ
    have h : Φf ψ = (hper ψ hψ).choose := by
      simp only [Φf]
      rw [dif_pos hψ]
    rw [h]
    exact (hper ψ hψ).choose_spec
  refine ⟨Ξ.biUnion Φf, ?_, ?_, ?_⟩
  · set B : ℝ := MvPolynomial.eval ![(D'' : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cH with hB
    set A : ℝ := MvPolynomial.eval ![(D'' : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] cY
      with hA
    have h1 : ((Ξ.biUnion Φf).card : ℝ) ≤ ∑ ψ ∈ Ξ, ((Φf ψ).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have h2 : ∑ ψ ∈ Ξ, ((Φf ψ).card : ℝ) ≤ ∑ _ψ ∈ Ξ, B :=
      Finset.sum_le_sum (fun ψ hψ => (hΦprops ψ hψ).1)
    have h3 : (∑ _ψ ∈ Ξ, B) = (Ξ.card : ℝ) * B := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h4 : (Ξ.card : ℝ) ≤ A := hΞcard
    have hAcard : (0 : ℝ) ≤ A := le_trans (Nat.cast_nonneg _) h4
    have hle : ((Ξ.biUnion Φf).card : ℝ) ≤ (Ξ.card : ℝ) * B := by
      rw [← h3]; linarith
    have hmain : ((Ξ.biUnion Φf).card : ℝ) ≤ A * (B * B + 1) := by
      by_cases hB0 : (0 : ℝ) ≤ B
      · have h5 : (Ξ.card : ℝ) * B ≤ A * B := mul_le_mul_of_nonneg_right h4 hB0
        have h6 : A * B ≤ A * (B * B + 1) :=
          mul_le_mul_of_nonneg_left (by nlinarith) hAcard
        linarith
      · have hB0' : B < 0 := not_le.mp hB0
        have hΞ0 : (Ξ.card : ℝ) = 0 := by
          have hnn : (0 : ℝ) ≤ (Ξ.card : ℝ) * B := le_trans (by positivity) hle
          nlinarith
        have hz : ((Ξ.biUnion Φf).card : ℝ) = 0 := by
          have hle0 : ((Ξ.biUnion Φf).card : ℝ) ≤ 0 := by
            rw [hΞ0, zero_mul] at hle; exact hle
          exact le_antisymm hle0 (by positivity)
        have h7 : (0 : ℝ) ≤ A * (B * B + 1) := by
          apply mul_nonneg hAcard; nlinarith
        linarith
    have hpt : (![((D'' : ℕ) : ℝ), (r : ℝ), (k : ℝ),
          -Real.log ε + Real.log 2] : Fin 4 → ℝ)
        = ![((D'' : ℕ) : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] := by
      funext i
      fin_cases i
      · simp
      · simp
      · simp
      · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
        rw [Real.log_div (ne_of_gt hε) (by norm_num : (2 : ℝ) ≠ 0)]
        ring_nf
    have hcY'm : MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cY' = A := by
      rw [hcY' D r k (-Real.log ε), hA, ← hD''q]
      exact congrArg (fun p : Fin 4 → ℝ => MvPolynomial.eval p cY) hpt
    have hcH'm : MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cH' = B := by
      rw [hcH' D r k (-Real.log ε), hB, ← hD''q, add_zero]
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_add, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, hcY'm, hcH'm]
    exact hmain
  · have hOK : ChartsOK S aH (MvPolynomial.eval ![D'', r] bH) r Set.univ Fc
        (Ξ.biUnion Φf) := by
      intro φ hφ
      obtain ⟨ψ, hψ, hφψ⟩ := Finset.mem_biUnion.mp hφ
      exact (hΦprops ψ hψ).2.1 φ hφψ
    have hdeg : MvPolynomial.eval ![D'', r] bH = MvPolynomial.eval ![D, r] bH' := by
      rw [hbH' D r, hD''q]
    rw [hdeg] at hOK
    refine ChartsOK_congr (G := Fc) ?_ ?_
    · intro i l t hl ht
      rw [hFc]
      simp only [paramClamp]
      rw [if_pos]
      intro w hw
      exact hval i l hl w hw
    · exact fun φ hφ => ⟨(hOK φ hφ).1, fun l hl => (hOK φ hφ).2 l trivial⟩
  · have hCov : Covers Set.univ Fc (Ξ.biUnion Φf) ε := by
      intro l _ x hx
      have hx0I : x 0 ∈ I := hx 0
      have hxt : Fin.tail x ∈ openCube n := fun j => hx j.succ
      obtain ⟨ψ, hψ, t, ht, hlt⟩ := hΞcov l trivial (x 0) hx0I (Fin.tail x) hxt
      obtain ⟨t', ht', φ, hφ, hlt'⟩ :=
        (hΦprops ψ hψ).2.2 l trivial (x 0) hx0I (Fin.tail x) hxt ⟨t, ht, hlt⟩
      refine ⟨φ, Finset.mem_biUnion.mpr ⟨ψ, hψ, hφ⟩, t', ht', fun i => ?_⟩
      have h' := hlt' i
      rwa [Fin.cons_self_tail x] at h'
    have hOK : ChartsOK S aH (MvPolynomial.eval ![D, r] bH') r Λ Fc (Ξ.biUnion Φf) := by
      have h0 : ChartsOK S aH (MvPolynomial.eval ![D'', r] bH) r Set.univ Fc
          (Ξ.biUnion Φf) := by
        intro φ hφ
        obtain ⟨ψ, hψ, hφψ⟩ := Finset.mem_biUnion.mp hφ
        exact (hΦprops ψ hψ).2.1 φ hφψ
      rw [show MvPolynomial.eval ![D'', r] bH = MvPolynomial.eval ![D, r] bH' from by
        rw [hbH' D r, hD''q]] at h0
      exact fun φ hφ => ⟨(h0 φ hφ).1, fun l hl => (h0 φ hφ).2 l trivial⟩
    refine Covers_congr (G := Fc) ?_ ?_ (fun l hl x hx => hCov l trivial x hx)
    · intro φ hφ l hl t ht
      exact ((hOK φ hφ).2 l hl).1 t ht
    · intro i l t hl ht
      rw [hFc]
      simp only [paramClamp]
      rw [if_pos]
      intro w hw
      exact hval i l hl w hw

/-- **The outer half of `StepLipHigh`.**  Given the per-chart step `StepLipHighPsi` as a family
over the parameter dimension (with the `hP1`-hypothesis supplied level by level), the `r ≥ 1`
slice `FLemPHigh S p (n+1) (PY p n)` follows by strong induction on the parameter dimension: at
level `q ≤ p` the `1`-Lipschitz hypothesis `hP1` at `q` is obtained from `hP1` at `p` by
`DescentP` (`PYLip` is a per-parameter-fibre condition, so it survives the parameter lift). -/
theorem FLemPHigh_of_Psi (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (n p : ℕ) (hn : 1 ≤ n) (h1 : ∀ q, Work.WilG4a.F1AffineW S q) (ih : ∀ q, FLem S q n)
    (hchoice : ChoiceHyp S) (hbdd : BddDxHyp S)
    (hP1 : FLemP S p (n + 1) (PYLip p n))
    (hPsi : ∀ (q : ℕ) (hP1q : FLemP S q (n + 1) (PYLip q n))
      (hind : ∀ m, m < q → FLemPHigh S m (n + 1) (PY m n)),
      PsiHyp S hcd hder n q hn h1 ih hchoice hbdd hP1q hind) :
    FLemPHigh S p (n + 1) (PY p n) := by
  have hmain : ∀ q, q ≤ p → FLemPHigh S q (n + 1) (PY q n) := by
    intro q
    refine Nat.strong_induction_on q ?_
    intro q' ih' hq'p
    have hP1' : FLemP S q' (n + 1) (PYLip q' n) :=
      DescentP S (n + 1) p q' hq'p (PYLip p n) (PYLip q' n)
        (fun r k F' hF' =>
          ⟨fun i l x hx m hm y hy =>
              hF'.1 i (fun j => l (Fin.castLE hq'p j)) x hx m hm y hy,
            fun i l z z' hz hz' =>
              hF'.2 i (fun j => l (Fin.castLE hq'p j)) z z' hz hz'⟩)
        hP1
    have hind' : ∀ m, m < q' → FLemPHigh S m (n + 1) (PY m n) :=
      fun m hm => ih' m hm (le_trans (Nat.le_of_lt hm) hq'p)
    exact FLemPHigh_at S hcd hder n q' hn h1 ih hchoice hbdd hP1' hind'
      (hPsi q' hP1' hind')
  exact hmain p le_rfl

end Work.WilkG4c
