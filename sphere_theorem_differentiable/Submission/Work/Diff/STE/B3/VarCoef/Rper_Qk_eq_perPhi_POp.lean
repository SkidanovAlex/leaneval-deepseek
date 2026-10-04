import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.perMatDefs
import Submission.Work.Diff.STE.B3.VarCoef.R_Qk_chartExpr_sym
import Submission.Work.Diff.STE.B3.QkDef
import Submission.Work.Diff.STE.B3.Comp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.VarCoef

/-!
# The periodised chart expansion of `R_l (Q_k h)` with the *periodised* chart matrix

`VarCoef.R_Qk_chartExpr_sym` expresses the localised component `D.R l (Qk D k h) a b` at a point `z`
through the chart matrix `D.mat l h` and the variable-coefficient operator `varLapPow k (A i) (B i)`:

`R_l(Q_k h)(z) = φ_l(z) · Σ_i Σ_{cd} co ⟨z⟩ · (varLapPow k A_i B_i)(Σ_{c'd'} ci ⟨·⟩ · mat_l h ⟨·⟩)(z)`.

The present file lifts this pointwise identity to the **periodised components** which the Fourier
theory of Layer A sees: on the torus the chart matrix is replaced by the genuinely `1`-periodic
cut-off chart matrix `perMat` (whose germ at `z` is the germ of `mat` at the translate `z + m`
whenever `ψ l` does not vanish there, and which is periodic with **no** smoothness hypothesis on
`η`), and the common prefactor `φ_l` by the periodised weight `perPhi`.  The result,

`D.Rper l (Q_k h) a b = M_{perPhi} (P perMat)`,

is the shape in which the flat lemma `VarCoef.varLapPow_cut_comm_pairing` can be applied: the
periodised objects are the ones whose Fourier coefficients are the `H^k` energies.

The proof is pointwise.  For a given `z` either no translate `z + m` lies in the support of `ψ l`
(then both sides vanish), or there is a unique such `m = m₀`.  In the second case the three
periodisations collapse to the corresponding un-periodised objects at `z + m₀`
(`Rper_eq_of_psi_ne`, `perPhi_eq_of_psi_ne`, `perMat_eventuallyEq`), the coefficients `co`, `ci`,
`A`, `B` are `1`-periodic so that they may be evaluated at `z` instead of `z + m₀`, and the
differential operator `varLapPow k` is local (`varLapPow_eventuallyEq`) and commutes with the
translation `w ↦ w + m₀` (`iterate_varLap_comp_add`).  The chart expression `hCE` at the point
`z + m₀` then closes the identity.

Only `η = 1` on the ball of radius `1/4` and `tsupport η ⊆ (-1/2,1/2)^n` are needed, exactly as in
`perMatDefs` -- in particular no smoothness of `η` is used.
-/

noncomputable section

/-! ## 1. The partial derivative and the variable-coefficient operator are local, and commute with
translation by a common period of the coefficients. -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The partial derivative commutes with a translation of the argument. -/
lemma pd_comp_add (a : ι) (G : (ι → ℝ) → ℂ) (v w : ι → ℝ) :
    Work.Diff.STE.pd a (fun u => G (u + v)) w = Work.Diff.STE.pd a G (w + v) := by
  simp only [Work.Diff.STE.pd, fderiv_comp_add_right]

/-- `varLap` only sees the germ. -/
lemma varLap_eventuallyEq {A : ι → ι → (ι → ℝ) → ℝ} {B : ι → (ι → ℝ) → ℝ}
    {F G : (ι → ℝ) → ℂ} {x : ι → ℝ} (h : F =ᶠ[nhds x] G) :
    Work.Diff.STE.B3.VarCoef.varLap A B F =ᶠ[nhds x] Work.Diff.STE.B3.VarCoef.varLap A B G := by
  have h2 : ∀ a, (fun y => Work.Diff.STE.pd a F y) =ᶠ[nhds x] (fun y => Work.Diff.STE.pd a G y) :=
    fun a => pd_eventuallyEq h a
  have h3 : ∀ a b, (fun y => Work.Diff.STE.pd a (Work.Diff.STE.pd b F) y) =ᶠ[nhds x]
      (fun y => Work.Diff.STE.pd a (Work.Diff.STE.pd b G) y) := by
    intro a b
    filter_upwards [Filter.EventuallyEq.fderiv (𝕜 := ℝ) (h2 b)] with y hy
    exact congrArg (fun (L : (ι → ℝ) →L[ℝ] ℂ) => L (Pi.single a 1)) hy
  have h4 : ∀ a, ∀ᶠ y in nhds x, ∀ b,
      Work.Diff.STE.pd a (Work.Diff.STE.pd b F) y = Work.Diff.STE.pd a (Work.Diff.STE.pd b G) y :=
    fun a => Filter.eventually_all.mpr (fun b => h3 a b)
  have h5 : ∀ a, ∀ᶠ y in nhds x,
      Work.Diff.STE.pd a F y = Work.Diff.STE.pd a G y := fun a => h2 a
  filter_upwards [Filter.eventually_all.mpr h4, Filter.eventually_all.mpr h5] with y hy hz
  simp only [Work.Diff.STE.B3.VarCoef.varLap, hy, hz]

/-- `varLap` commutes with a translation when the coefficients are invariant under it. -/
lemma varLap_comp_add {A : ι → ι → (ι → ℝ) → ℝ} {B : ι → (ι → ℝ) → ℝ} {G : (ι → ℝ) → ℂ}
    {v : ι → ℝ} (hA : ∀ a b w, A a b (w + v) = A a b w) (hB : ∀ a w, B a (w + v) = B a w) :
    Work.Diff.STE.B3.VarCoef.varLap A B (fun u => G (u + v))
      = fun w => Work.Diff.STE.B3.VarCoef.varLap A B G (w + v) := by
  have key : ∀ a b, ∀ w, Work.Diff.STE.pd a (Work.Diff.STE.pd b (fun u => G (u + v))) w
      = Work.Diff.STE.pd a (Work.Diff.STE.pd b G) (w + v) := by
    intro a b w
    have hfun : Work.Diff.STE.pd b (fun u => G (u + v))
        = (fun y => Work.Diff.STE.pd b G (y + v)) := funext (fun y => pd_comp_add b G v y)
    rw [hfun]
    exact pd_comp_add a (Work.Diff.STE.pd b G) v w
  funext w
  simp only [Work.Diff.STE.B3.VarCoef.varLap]
  have h1 : (∑ a, ∑ b, ((A a b w : ℝ) : ℂ)
        * Work.Diff.STE.pd a (Work.Diff.STE.pd b (fun u => G (u + v))) w)
      = ∑ a, ∑ b, ((A a b (w + v) : ℝ) : ℂ)
          * Work.Diff.STE.pd a (Work.Diff.STE.pd b G) (w + v) := by
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hA a b w, key a b w]
  have h2 : (∑ a, ((B a w : ℝ) : ℂ) * Work.Diff.STE.pd a (fun u => G (u + v)) w)
      = ∑ a, ((B a (w + v) : ℝ) : ℂ) * Work.Diff.STE.pd a G (w + v) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hB a w, pd_comp_add a G v w]
  rw [h1, h2]

/-- Powers of `varLap` commute with a translation when the coefficients are invariant under it. -/
lemma iterate_varLap_comp_add {A : ι → ι → (ι → ℝ) → ℝ} {B : ι → (ι → ℝ) → ℝ} {v : ι → ℝ}
    (hA : ∀ a b w, A a b (w + v) = A a b w) (hB : ∀ a w, B a (w + v) = B a w) (k : ℕ)
    (G : (ι → ℝ) → ℂ) :
    Work.Diff.STE.B3.VarCoef.varLapPow k A B (fun u => G (u + v))
      = fun w => Work.Diff.STE.B3.VarCoef.varLapPow k A B G (w + v) := by
  induction k generalizing G with
  | zero => funext w; rfl
  | succ k ih =>
    have hL : Work.Diff.STE.B3.VarCoef.varLapPow (Nat.succ k) A B (fun u => G (u + v))
        = Work.Diff.STE.B3.VarCoef.varLap A B
            (Work.Diff.STE.B3.VarCoef.varLapPow k A B (fun u => G (u + v))) :=
      Function.iterate_succ_apply' _ k _
    rw [hL, ih G, varLap_comp_add hA hB]
    funext w
    rw [show Work.Diff.STE.B3.VarCoef.varLapPow (Nat.succ k) A B G
        = Work.Diff.STE.B3.VarCoef.varLap A B (Work.Diff.STE.B3.VarCoef.varLapPow k A B G) from
      Function.iterate_succ_apply' _ k _]

/-- `varLapPow` only sees the germ. -/
lemma varLapPow_eventuallyEq {A : ι → ι → (ι → ℝ) → ℝ} {B : ι → (ι → ℝ) → ℝ}
    {F G : (ι → ℝ) → ℂ} {x : ι → ℝ} (h : F =ᶠ[nhds x] G) (k : ℕ) :
    Work.Diff.STE.B3.VarCoef.varLapPow k A B F
      =ᶠ[nhds x] Work.Diff.STE.B3.VarCoef.varLapPow k A B G := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [show Work.Diff.STE.B3.VarCoef.varLapPow (Nat.succ k) A B F
        = Work.Diff.STE.B3.VarCoef.varLap A B (Work.Diff.STE.B3.VarCoef.varLapPow k A B F) from
      Function.iterate_succ_apply' _ k _,
      show Work.Diff.STE.B3.VarCoef.varLapPow (Nat.succ k) A B G
        = Work.Diff.STE.B3.VarCoef.varLap A B (Work.Diff.STE.B3.VarCoef.varLapPow k A B G) from
      Function.iterate_succ_apply' _ k _]
    exact varLap_eventuallyEq ih

end Generic

/-! ## 2. The periodisations of the chart objects -/

section ChartPeriodisation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- On the support of `ψ l`, the flat coordinate has norm at most `1/4`. -/
lemma norm_le_quarter_of_psi_ne (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) {l : ι₀}
    {y : Fin (Module.finrank ℝ E) → ℝ} (hy : D.psi l y ≠ 0) : ‖y‖ ≤ 1 / 4 := by
  have h1 : ‖y‖ < D.σ l := Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero D hy
  have h2 : 2 * D.σ l ≤ 1 / 4 := D.hσ2 l
  linarith

/-- The periodisation of a localised component is `1`-periodic. -/
lemma Rper_periodic (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.Periodic1 (D.Rper i h a b) :=
  Work.Diff.STE.periodization_periodic
    (fun w : Fin (Module.finrank ℝ E) → ℝ => ((D.R i h a b w : ℝ) : ℂ))

/-- The periodisation of the chart weight `ψ l · √dens l` is `1`-periodic. -/
lemma perPhi_periodic (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (l : ι₀) :
    Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.perPhi D l) :=
  Work.Diff.STE.periodization_periodic
    (fun w : Fin (Module.finrank ℝ E) → ℝ => ((D.psi l w * Real.sqrt (D.dens l w) : ℝ) : ℂ))

/-- The periodisation of the cut-off chart matrix `η · mat l h a b` is `1`-periodic. -/
lemma perMat_periodic (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (l : ι₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.perMat D η l h a b) :=
  Work.Diff.STE.periodization_periodic
    (fun w : Fin (Module.finrank ℝ E) → ℝ => ((η w * D.mat l h a b w : ℝ) : ℂ))

/-- At a point `z` whose translate `z + m` lies in the support of `ψ l`, the periodised component
is the localised component at that translate. -/
lemma Rper_eq_of_psi_ne (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (l : ι₀)
    (a b : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    {m : Fin (Module.finrank ℝ E) → ℤ} (hm : D.psi l (z + Work.Diff.STE.iVec m) ≠ 0) :
    D.Rper l h a b z = ((D.R l h a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ) := by
  have hper : D.Rper l h a b (z + Work.Diff.STE.iVec m) = D.Rper l h a b z :=
    Work.Diff.STE.B3.Periodic1_iVec (Rper_periodic D l h a b) m z
  rw [← hper]
  exact Work.Diff.STE.B3.Rper_eq_of_mem_cube D h l a b
    (fun k => D.psi_supp l (Function.mem_support.mpr hm) k (Set.mem_univ k))

/-- At a point `z` whose translate `z + m` lies in the support of `ψ l`, the periodised weight is
the weight at that translate. -/
lemma perPhi_eq_of_psi_ne (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (l : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ} {m : Fin (Module.finrank ℝ E) → ℤ}
    (hm : D.psi l (z + Work.Diff.STE.iVec m) ≠ 0) :
    Work.Diff.STE.B3.perPhi D l z
      = ((D.psi l (z + Work.Diff.STE.iVec m)
          * Real.sqrt (D.dens l (z + Work.Diff.STE.iVec m)) : ℝ) : ℂ) := by
  have hper : Work.Diff.STE.B3.perPhi D l (z + Work.Diff.STE.iVec m)
      = Work.Diff.STE.B3.perPhi D l z :=
    Work.Diff.STE.B3.Periodic1_iVec (perPhi_periodic D l) m z
  rw [← hper]
  exact Work.Diff.STE.B3.perPhi_eq_of_mem_ball D l (norm_le_quarter_of_psi_ne D hm)

/-- Near a point `z` whose translate `z + m` lies in the support of `ψ l`, the periodised cut-off
chart matrix agrees with the chart matrix at the translate. -/
lemma perMat_eventuallyEq (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hη1 : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 1 / 4 → η z = 1)
    (hηt : tsupport η ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (l : ι₀) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (a b : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    {m : Fin (Module.finrank ℝ E) → ℤ} (hm : D.psi l (z + Work.Diff.STE.iVec m) ≠ 0) :
    ∀ᶠ w in nhds z, Work.Diff.STE.B3.perMat D η l h a b w
      = ((D.mat l h a b (w + Work.Diff.STE.iVec m) : ℝ) : ℂ) := by
  have hlt : ‖z + Work.Diff.STE.iVec m‖ < 1 / 4 := by
    have h1 : ‖z + Work.Diff.STE.iVec m‖ < D.σ l :=
      Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero D hm
    have h2 : 2 * D.σ l ≤ 1 / 4 := D.hσ2 l
    linarith
  have hgerm : ∀ᶠ u in nhds (z + Work.Diff.STE.iVec m),
      Work.Diff.STE.B3.perMat D η l h a b u = ((D.mat l h a b u : ℝ) : ℂ) :=
    Filter.eventually_of_mem
      ((Metric.isOpen_ball (x := (0 : Fin (Module.finrank ℝ E) → ℝ)) (ε := 1 / 4)).mem_nhds
        (by simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hlt))
      (fun u hu => Work.Diff.STE.B3.perMat_eq_of_mem_ball D η hη1 hηt l h a b
        (le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hu)))
  have hpull : ∀ᶠ w in nhds z, Work.Diff.STE.B3.perMat D η l h a b (w + Work.Diff.STE.iVec m)
      = ((D.mat l h a b (w + Work.Diff.STE.iVec m) : ℝ) : ℂ) :=
    Filter.Tendsto.eventually ((continuous_add_const (Work.Diff.STE.iVec m)).tendsto z) hgerm
  filter_upwards [hpull] with w hw
  rw [← hw]
  exact (Work.Diff.STE.B3.Periodic1_iVec (perMat_periodic D η l h a b) m w).symm

end ChartPeriodisation

theorem Rper_Qk_eq_perPhi_POp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (k : ℕ) (l : ι₀)
    (η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hη1 : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 1 / 4 → η z = 1)
    (hηt : tsupport η ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (A : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (B : ι₀ → Fin (Module.finrank ℝ E) → (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (ci co : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hA : ∀ i a b, ContDiff ℝ (⊤ : ℕ∞) (A i a b))
    (hAp : ∀ i a b, Work.Diff.STE.Periodic1 (A i a b))
    (hB : ∀ i a, ContDiff ℝ (⊤ : ℕ∞) (B i a))
    (hBp : ∀ i a, Work.Diff.STE.Periodic1 (B i a))
    (hci : ∀ i c d c' d', ContDiff ℝ (⊤ : ℕ∞) (ci i c d c' d'))
    (hcip : ∀ i c d c' d', Work.Diff.STE.Periodic1 (ci i c d c' d'))
    (hco : ∀ i a b c d, ContDiff ℝ (⊤ : ℕ∞) (co i a b c d))
    (hcop : ∀ i a b c d, Work.Diff.STE.Periodic1 (co i a b c d))
    (hCE : ∀ (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)),
      (∀ (j : ι₀) (a' b' : Fin (Module.finrank ℝ E)),
        ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R j h a' b')) →
      ∀ z : Fin (Module.finrank ℝ E) → ℝ,
        ((D.R l (Work.Diff.STE.B3.Qk D k h) a b z : ℝ) : ℂ) =
          ((D.psi l z * Real.sqrt (D.dens l z) : ℝ) : ℂ) *
            (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              ((co i a b c d z : ℝ) : ℂ) *
                Work.Diff.STE.B3.VarCoef.varLapPow k (A i) (B i)
                  (fun w => ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                    ((ci i c d c' d' w : ℝ) : ℂ) *
                      ((D.mat l h c' d' w : ℝ) : ℂ)) z))
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E))
    (hh : ∀ (j : ι₀) (a' b' : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R j h a' b')) :
    D.Rper l (Work.Diff.STE.B3.Qk D k h) a b
      = fun z => Work.Diff.STE.B3.perPhi (I := I) (M := M) D l z *
          (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            ((co i a b c d z : ℝ) : ℂ) *
              Work.Diff.STE.B3.VarCoef.varLapPow k (A i) (B i)
                (fun w => ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                  ((ci i c d c' d' w : ℝ) : ℂ) *
                    Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h c' d' w) z) := by
  funext z
  by_cases hS : ∃ m : Fin (Module.finrank ℝ E) → ℤ,
      D.psi l (z + Work.Diff.STE.iVec m) ≠ 0
  · -- there is a unique translate `m₀` with `ψ l (z + m₀) ≠ 0`: everything is computed there
    obtain ⟨m₀, hm₀⟩ := hS
    have hL : D.Rper l (Work.Diff.STE.B3.Qk D k h) a b z
        = ((D.R l (Work.Diff.STE.B3.Qk D k h) a b
            (z + Work.Diff.STE.iVec m₀) : ℝ) : ℂ) :=
      Rper_eq_of_psi_ne D (Work.Diff.STE.B3.Qk D k h) l a b hm₀
    have hPhi : Work.Diff.STE.B3.perPhi D l z
        = ((D.psi l (z + Work.Diff.STE.iVec m₀)
            * Real.sqrt (D.dens l (z + Work.Diff.STE.iVec m₀)) : ℝ) : ℂ) :=
      perPhi_eq_of_psi_ne D l hm₀
    -- the operator applied to the periodised data at `z` is the operator applied to the chart
    -- matrix at `z + m₀`
    have hG : (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          ((co i a b c d z : ℝ) : ℂ) *
            Work.Diff.STE.B3.VarCoef.varLapPow k (A i) (B i)
              (fun w => ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                ((ci i c d c' d' w : ℝ) : ℂ) *
                  Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h c' d' w) z)
        = (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          ((co i a b c d (z + Work.Diff.STE.iVec m₀) : ℝ) : ℂ) *
            Work.Diff.STE.B3.VarCoef.varLapPow k (A i) (B i)
              (fun w => ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                ((ci i c d c' d' w : ℝ) : ℂ) *
                  ((D.mat l h c' d' w : ℝ) : ℂ))
              (z + Work.Diff.STE.iVec m₀)) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun c _ =>
        Finset.sum_congr rfl (fun d _ => ?_)))
      have hco' : ((co i a b c d (z + Work.Diff.STE.iVec m₀) : ℝ) : ℂ)
          = ((co i a b c d z : ℝ) : ℂ) := by
        rw [Work.Diff.STE.B3.Periodic1_iVec (hcop i a b c d) m₀ z]
      have hV : Work.Diff.STE.B3.VarCoef.varLapPow k (A i) (B i)
            (fun w => ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
              ((ci i c d c' d' w : ℝ) : ℂ) *
                Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h c' d' w) z
          = Work.Diff.STE.B3.VarCoef.varLapPow k (A i) (B i)
            (fun w => ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
              ((ci i c d c' d' w : ℝ) : ℂ) * ((D.mat l h c' d' w : ℝ) : ℂ))
            (z + Work.Diff.STE.iVec m₀) := by
        -- locality: `perMat` agrees with the translate of `mat` near `z`
        have hinner : ∀ c' d' : Fin (Module.finrank ℝ E),
            (fun w : Fin (Module.finrank ℝ E) → ℝ =>
              ((ci i c d c' d' w : ℝ) : ℂ) *
                Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h c' d' w)
            =ᶠ[nhds z] (fun w : Fin (Module.finrank ℝ E) → ℝ =>
              ((ci i c d c' d' w : ℝ) : ℂ) *
                ((D.mat l h c' d' (w + Work.Diff.STE.iVec m₀) : ℝ) : ℂ)) := by
          intro c' d'
          filter_upwards [perMat_eventuallyEq D η hη1 hηt l h c' d' hm₀] with w hw
          rw [hw]
        have hgerm : (fun w : Fin (Module.finrank ℝ E) → ℝ =>
              ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                ((ci i c d c' d' w : ℝ) : ℂ) *
                  Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h c' d' w)
            =ᶠ[nhds z] (fun w : Fin (Module.finrank ℝ E) → ℝ =>
              ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                ((ci i c d c' d' w : ℝ) : ℂ) *
                  ((D.mat l h c' d' (w + Work.Diff.STE.iVec m₀) : ℝ) : ℂ)) := by
          filter_upwards [Filter.eventually_all.mpr (fun c' =>
            Filter.eventually_all.mpr (fun d' => hinner c' d'))] with w hw
          refine Finset.sum_congr rfl (fun c' _ => Finset.sum_congr rfl (fun d' _ => ?_))
          exact hw c' d'
        rw [(varLapPow_eventuallyEq (A := A i) (B := B i) hgerm k).eq_of_nhds]
        -- translation: the coefficients are `1`-periodic
        have hAper : ∀ a' b' (w : Fin (Module.finrank ℝ E) → ℝ),
            A i a' b' (w + Work.Diff.STE.iVec m₀) = A i a' b' w :=
          fun a' b' w => Work.Diff.STE.B3.Periodic1_iVec (hAp i a' b') m₀ w
        have hBper : ∀ a' (w : Fin (Module.finrank ℝ E) → ℝ),
            B i a' (w + Work.Diff.STE.iVec m₀) = B i a' w :=
          fun a' w => Work.Diff.STE.B3.Periodic1_iVec (hBp i a') m₀ w
        have hshift : (fun w : Fin (Module.finrank ℝ E) → ℝ =>
              ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                ((ci i c d c' d' w : ℝ) : ℂ) *
                  ((D.mat l h c' d' (w + Work.Diff.STE.iVec m₀) : ℝ) : ℂ))
            = (fun w : Fin (Module.finrank ℝ E) → ℝ =>
              ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                ((ci i c d c' d' (w + Work.Diff.STE.iVec m₀) : ℝ) : ℂ) *
                  ((D.mat l h c' d' (w + Work.Diff.STE.iVec m₀) : ℝ) : ℂ)) := by
          funext w
          refine Finset.sum_congr rfl (fun c' _ => Finset.sum_congr rfl (fun d' _ => ?_))
          rw [Work.Diff.STE.B3.Periodic1_iVec (hcip i c d c' d') m₀ w]
        rw [hshift, iterate_varLap_comp_add hAper hBper k
          (fun u => ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
              ((ci i c d c' d' u : ℝ) : ℂ) * ((D.mat l h c' d' u : ℝ) : ℂ))]
      rw [← hco', hV]
    rw [hL, hPhi, hG]
    exact hCE h a b hh (z + Work.Diff.STE.iVec m₀)
  · -- no translate of `z` lies in the support of `ψ l`: both sides vanish
    have hS' : ∀ m : Fin (Module.finrank ℝ E) → ℤ,
        D.psi l (z + Work.Diff.STE.iVec m) = 0 := fun m => by
      by_contra hh'
      exact hS ⟨m, hh'⟩
    have hL0 : D.Rper l (Work.Diff.STE.B3.Qk D k h) a b z = 0 := by
      rw [show D.Rper l (Work.Diff.STE.B3.Qk D k h) a b z
          = ∑' m : Fin (Module.finrank ℝ E) → ℤ,
              ((D.R l (Work.Diff.STE.B3.Qk D k h) a b
                (z + Work.Diff.STE.iVec m) : ℝ) : ℂ) from rfl]
      have hz : ∀ m : Fin (Module.finrank ℝ E) → ℤ,
          ((D.R l (Work.Diff.STE.B3.Qk D k h) a b
            (z + Work.Diff.STE.iVec m) : ℝ) : ℂ) = 0 := fun m => by
        simp only [Work.Diff.STE.B3Data.R, hS' m, zero_mul, Complex.ofReal_zero]
      simp only [hz, tsum_zero]
    have hPhi0 : Work.Diff.STE.B3.perPhi D l z = 0 := by
      rw [show Work.Diff.STE.B3.perPhi D l z
          = ∑' m : Fin (Module.finrank ℝ E) → ℤ,
              ((D.psi l (z + Work.Diff.STE.iVec m)
                * Real.sqrt (D.dens l (z + Work.Diff.STE.iVec m)) : ℝ) : ℂ) from rfl]
      have hz : ∀ m : Fin (Module.finrank ℝ E) → ℤ,
          ((D.psi l (z + Work.Diff.STE.iVec m)
            * Real.sqrt (D.dens l (z + Work.Diff.STE.iVec m)) : ℝ) : ℂ) = 0 := fun m => by
        simp only [hS' m, zero_mul, Complex.ofReal_zero]
      simp only [hz, tsum_zero]
    rw [hL0, hPhi0, zero_mul]

end

end Work.Diff.STE.B3.VarCoef
