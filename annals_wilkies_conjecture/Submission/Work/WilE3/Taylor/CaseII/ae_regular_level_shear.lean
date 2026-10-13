import Mathlib

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / CaseII: the "generic regularity of a level
  sheet of a shear" lemma.

  Statement.  Let `U ⊆ ℝ^{e+1}` be open, let `A : ℝ^{e+1} → ℝ^e`, `φ : ℝ^{e+1} → ℝ` and
  `b : ℝ^{e+1} → (ℝ^{P'} →L ℝ^e)` be `C¹` on `U`.  Then for almost every pair
  `wv = (w₁, w₂) ∈ ℝ^e × ℝ^{P'}` (with respect to Lebesgue measure) and almost every
  `c ∈ ℝ`, every `x ∈ U` satisfying

      `A x + b x w₂ + w₁ = 0`,  `φ x = c`

  is a point at which the combined map `ξ ↦ (dφ_x ξ, d(A + b·w₂)_x ξ)` is injective.

  Proof technique.  This is Sard's lemma in disguise.  Consider the `C¹` map
  `g : ((ℝ^e × ℝ^{P'}) × ℝ) → ((ℝ^e × ℝ^{P'}) × ℝ)`,

      `g ((y, w), λ) = ((-(A (snoc y λ) + b (snoc y λ) w), w), φ (snoc y λ))`,

  whose domain coordinates encode the "input" `(x, w₂)` via `x = snoc y λ`, and whose target
  coordinates are `(w₁, w₂, c)`.  Its Fréchet derivative at a non-critical-ish point carries a
  vector `ξ ∈ ℝ^{e+1}` (placed in the `(y, λ)` slots, with the `w` slot set to `0`) to
  `(-(dA_x ξ + (db_x ξ) w₂), 0, dφ_x ξ)`; consequently, whenever the map
  `ξ ↦ (dφ_x ξ, d(A + b·w₂)_x ξ)` fails to be injective, `g` is critical there.  The set of
  values `(w₁, w₂, c)` at which a bad point of `U` exists is therefore contained in the image of
  the critical set of `g`, which `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` (Mathlib's
  fixed-dimension Sard lemma) shows to be Lebesgue-null.  Fubini (`Measure.ae_ae_of_ae_prod`)
  converts this nullity into the two nested "almost everywhere" assertions.
-/

noncomputable section

open scoped Topology
open MeasureTheory

namespace Work.WilE3.Taylor.CaseII

namespace Shear

/-- The ambient space of the shear map: coordinates `(w₁, w₂, c)` — nested as
`((w₁, w₂), c)` to match the shape of the statement's quantifiers. -/
abbrev Spc (e P' : ℕ) := ((Fin e → ℝ) × (Fin P' → ℝ)) × ℝ

/-- The linear map `(Fin n → ℝ) × ℝ → (Fin (n+1) → ℝ)` given by appending the last coordinate. -/
def snocLM (n : ℕ) : (Fin n → ℝ) × ℝ →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun p := Fin.snoc p.1 p.2
  map_add' p q := by
    ext i
    induction i using Fin.lastCases with
    | last => simp
    | cast j => simp
  map_smul' c p := by
    ext i
    induction i using Fin.lastCases with
    | last => simp
    | cast j => simp

/-- `Fin.snoc` as a continuous linear map. -/
def snocCLM (n : ℕ) : (Fin n → ℝ) × ℝ →L[ℝ] (Fin (n + 1) → ℝ) :=
  (snocLM n).toContinuousLinearMap

/-- Projection onto the first `e` coordinates of the `x`-slot. -/
def fstfst (e P' : ℕ) : Spc e P' →L[ℝ] (Fin e → ℝ) :=
  (ContinuousLinearMap.fst ℝ (Fin e → ℝ) (Fin P' → ℝ)).comp
    (ContinuousLinearMap.fst ℝ ((Fin e → ℝ) × (Fin P' → ℝ)) ℝ)

/-- Projection onto the last coordinate of the `x`-slot. -/
def sndsnd (e P' : ℕ) : Spc e P' →L[ℝ] ℝ :=
  ContinuousLinearMap.snd ℝ ((Fin e → ℝ) × (Fin P' → ℝ)) ℝ

/-- Projection onto the `w₂` coordinate. -/
def Wproj (e P' : ℕ) : Spc e P' →L[ℝ] (Fin P' → ℝ) :=
  (ContinuousLinearMap.snd ℝ (Fin e → ℝ) (Fin P' → ℝ)).comp
    (ContinuousLinearMap.fst ℝ ((Fin e → ℝ) × (Fin P' → ℝ)) ℝ)

/-- The map `((y, w), λ) ↦ snoc y λ`, i.e. reassembling the `x`-coordinate. -/
def Jproj (e P' : ℕ) : Spc e P' →L[ℝ] (Fin (e+1) → ℝ) :=
  (snocCLM e).comp (ContinuousLinearMap.prod (fstfst e P') (sndsnd e P'))

lemma Jproj_apply (e P' : ℕ) (y : Fin e → ℝ) (w : Fin P' → ℝ) (lam : ℝ) :
    Jproj e P' ((y, w), lam) = Fin.snoc y lam := rfl

lemma Wproj_apply (e P' : ℕ) (y : Fin e → ℝ) (w : Fin P' → ℝ) (lam : ℝ) :
    Wproj e P' ((y, w), lam) = w := rfl

/-- The shear map attached to `A`, `b`, `φ`. -/
def g {e P' : ℕ} (A : (Fin (e+1) → ℝ) → (Fin e → ℝ))
    (b : (Fin (e+1) → ℝ) → (Fin P' → ℝ) →L[ℝ] (Fin e → ℝ))
    (φ : (Fin (e+1) → ℝ) → ℝ) : Spc e P' → Spc e P' :=
  fun u => ((-(A (Jproj e P' u) + b (Jproj e P' u) (Wproj e P' u)), Wproj e P' u),
            φ (Jproj e P' u))

/-- The explicit Fréchet derivative of `g` at `u`. -/
def Dg {e P' : ℕ} (A : (Fin (e+1) → ℝ) → (Fin e → ℝ))
    (b : (Fin (e+1) → ℝ) → (Fin P' → ℝ) →L[ℝ] (Fin e → ℝ))
    (φ : (Fin (e+1) → ℝ) → ℝ) (u : Spc e P') : Spc e P' →L[ℝ] Spc e P' :=
  ContinuousLinearMap.prod
    (ContinuousLinearMap.prod
      (-((fderiv ℝ A (Jproj e P' u)).comp (Jproj e P')
        + ((b (Jproj e P' u)).comp (Wproj e P')
           + ((fderiv ℝ b (Jproj e P' u)).comp (Jproj e P')).flip (Wproj e P' u))))
      (Wproj e P'))
    ((fderiv ℝ φ (Jproj e P' u)).comp (Jproj e P'))

/-- Differentiability of the shear map at points whose `x`-coordinate lies in `U`. -/
theorem hasFDerivAt_g {e P'} (A : (Fin (e+1) → ℝ) → (Fin e → ℝ))
    (b : (Fin (e+1) → ℝ) → (Fin P' → ℝ) →L[ℝ] (Fin e → ℝ))
    (φ : (Fin (e+1) → ℝ) → ℝ) (u : Spc e P')
    (hA : HasFDerivAt A (fderiv ℝ A (Jproj e P' u)) (Jproj e P' u))
    (hb : HasFDerivAt b (fderiv ℝ b (Jproj e P' u)) (Jproj e P' u))
    (hφ : HasFDerivAt φ (fderiv ℝ φ (Jproj e P' u)) (Jproj e P' u)) :
    HasFDerivAt (g A b φ) (Dg A b φ u) u := by
  have h1 : HasFDerivAt (fun u => A (Jproj e P' u))
      ((fderiv ℝ A (Jproj e P' u)).comp (Jproj e P')) u :=
    hA.comp u (Jproj e P').hasFDerivAt
  have h2 : HasFDerivAt (fun u => b (Jproj e P' u))
      ((fderiv ℝ b (Jproj e P' u)).comp (Jproj e P')) u :=
    hb.comp u (Jproj e P').hasFDerivAt
  have h3 : HasFDerivAt (fun u => b (Jproj e P' u) (Wproj e P' u))
      ((b (Jproj e P' u)).comp (Wproj e P')
        + ((fderiv ℝ b (Jproj e P' u)).comp (Jproj e P')).flip (Wproj e P' u)) u :=
    h2.clm_apply (Wproj e P').hasFDerivAt
  have h13 : HasFDerivAt (fun u => A (Jproj e P' u) + b (Jproj e P' u) (Wproj e P' u))
      ((fderiv ℝ A (Jproj e P' u)).comp (Jproj e P')
        + ((b (Jproj e P' u)).comp (Wproj e P')
           + ((fderiv ℝ b (Jproj e P' u)).comp (Jproj e P')).flip (Wproj e P' u))) u :=
    h1.add h3
  have h4 : HasFDerivAt (fun u => -(A (Jproj e P' u) + b (Jproj e P' u) (Wproj e P' u)))
      (-((fderiv ℝ A (Jproj e P' u)).comp (Jproj e P')
        + ((b (Jproj e P' u)).comp (Wproj e P')
           + ((fderiv ℝ b (Jproj e P' u)).comp (Jproj e P')).flip (Wproj e P' u)))) u :=
    h13.neg
  have h5 : HasFDerivAt (fun u => φ (Jproj e P' u))
      ((fderiv ℝ φ (Jproj e P' u)).comp (Jproj e P')) u :=
    hφ.comp u (Jproj e P').hasFDerivAt
  have h6 := h4.prodMk (Wproj e P').hasFDerivAt
  exact h6.prodMk h5

/-- **The critical-point criterion.** If the combined derivative
`ξ ↦ (dφ_x ξ, d(A + b·w₂)_x ξ)` is not injective at `x = Jproj u`, `w₂ = Wproj u`, then the
Fréchet derivative of the shear map `g` at `u` is singular. -/
theorem det_fderiv_g_eq_zero {e P'} (A : (Fin (e+1) → ℝ) → (Fin e → ℝ))
    (b : (Fin (e+1) → ℝ) → (Fin P' → ℝ) →L[ℝ] (Fin e → ℝ))
    (φ : (Fin (e+1) → ℝ) → ℝ) (u : Spc e P')
    (hA : HasFDerivAt A (fderiv ℝ A (Jproj e P' u)) (Jproj e P' u))
    (hb : HasFDerivAt b (fderiv ℝ b (Jproj e P' u)) (Jproj e P' u))
    (hφ : HasFDerivAt φ (fderiv ℝ φ (Jproj e P' u)) (Jproj e P' u))
    (hn : ¬ Function.Injective (fun ξ : Fin (e+1) → ℝ =>
        (fderiv ℝ φ (Jproj e P' u) ξ,
         fderiv ℝ (fun z => A z + b z (Wproj e P' u)) (Jproj e P' u) ξ))) :
    (fderiv ℝ (g A b φ) u).det = 0 := by
  rw [Function.Injective] at hn
  push_neg at hn
  obtain ⟨a₁, a₂, heq, hne⟩ := hn
  have hφeq : fderiv ℝ φ (Jproj e P' u) a₁ = fderiv ℝ φ (Jproj e P' u) a₂ := by
    simpa using congrArg Prod.fst heq
  have hKeq : fderiv ℝ (fun z => A z + b z (Wproj e P' u)) (Jproj e P' u) a₁
      = fderiv ℝ (fun z => A z + b z (Wproj e P' u)) (Jproj e P' u) a₂ := by
    simpa using congrArg Prod.snd heq
  set ξ : Fin (e+1) → ℝ := a₁ - a₂ with hξdef
  have hξne : ξ ≠ 0 := by rw [hξdef]; exact sub_ne_zero.mpr hne
  have hφξ : fderiv ℝ φ (Jproj e P' u) ξ = 0 := by rw [hξdef, map_sub, hφeq, sub_self]
  have hKξ : fderiv ℝ (fun z => A z + b z (Wproj e P' u)) (Jproj e P' u) ξ = 0 := by
    rw [hξdef, map_sub, hKeq, sub_self]
  have hbw : HasFDerivAt (fun z => b z (Wproj e P' u))
      ((fderiv ℝ b (Jproj e P' u)).flip (Wproj e P' u)) (Jproj e P' u) := by
    have h := hb.clm_apply (hasFDerivAt_const (x := Jproj e P' u) (Wproj e P' u))
    simpa using h
  have hsum : fderiv ℝ (fun z => A z + b z (Wproj e P' u)) (Jproj e P' u)
      = fderiv ℝ A (Jproj e P' u) + (fderiv ℝ b (Jproj e P' u)).flip (Wproj e P' u) :=
    (hA.add hbw).fderiv
  have hdAdb : fderiv ℝ A (Jproj e P' u) ξ + (fderiv ℝ b (Jproj e P' u) ξ) (Wproj e P' u) = 0 := by
    have h := hKξ
    rw [hsum] at h
    simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply] using h
  set v : Spc e P' := ((Fin.init ξ, 0), ξ (Fin.last e)) with hvdef
  have hJv : Jproj e P' v = ξ := by rw [hvdef]; exact Fin.snoc_init_self ξ
  have hWv : Wproj e P' v = 0 := rfl
  have hv_ne : v ≠ 0 := by
    intro hv0
    have : Jproj e P' v = 0 := by rw [hv0]; simp
    rw [hJv] at this
    exact hξne this
  have hzero : fderiv ℝ (g A b φ) u v = 0 := by
    rw [(hasFDerivAt_g A b φ u hA hb hφ).fderiv]
    simp only [Dg, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply,
      hJv, hWv, hφξ, map_zero]
    rw [zero_add, hdAdb, neg_zero]
    rfl
  have hker : (fderiv ℝ (g A b φ) u).toLinearMap.ker ≠ ⊥ := by
    intro hbot
    have hv : v ∈ (fderiv ℝ (g A b φ) u).toLinearMap.ker := by
      rw [LinearMap.mem_ker]; exact hzero
    rw [hbot, Submodule.mem_bot] at hv
    exact hv_ne hv
  have hdet : LinearMap.det (fderiv ℝ (g A b φ) u).toLinearMap = 0 :=
    LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker
  exact hdet

end Shear

open Shear

theorem ae_regular_level_shear {e P' : ℕ} (U : Set (Fin (e + 1) → ℝ)) (hU : IsOpen U)
    (A : (Fin (e + 1) → ℝ) → (Fin e → ℝ))
    (b : (Fin (e + 1) → ℝ) → (Fin P' → ℝ) →L[ℝ] (Fin e → ℝ))
    (φ : (Fin (e + 1) → ℝ) → ℝ)
    (hA : ContDiffOn ℝ 1 A U) (hb : ContDiffOn ℝ 1 b U) (hφ : ContDiffOn ℝ 1 φ U) :
    ∀ᵐ wv : (Fin e → ℝ) × (Fin P' → ℝ), ∀ᵐ c : ℝ, ∀ x ∈ U,
      A x + b x wv.2 + wv.1 = 0 → φ x = c →
      Function.Injective (fun ξ : Fin (e + 1) → ℝ =>
        (fderiv ℝ φ x ξ, fderiv ℝ (fun z => A z + b z wv.2) x ξ)) := by
  haveI hH1 : Measure.IsAddLeftInvariant (volume : Measure ((Fin e → ℝ) × (Fin P' → ℝ))) :=
    Measure.prod.instIsAddLeftInvariant (μ := volume) (ν := volume)
  haveI hH2 : Measure.IsAddLeftInvariant (volume : Measure (Spc e P')) :=
    Measure.prod.instIsAddLeftInvariant (μ := volume) (ν := volume)
  haveI hHaar : Measure.IsAddHaarMeasure (volume : Measure (Spc e P')) := ⟨⟩
  have hdiff : ∀ u : Spc e P', Jproj e P' u ∈ U →
      HasFDerivAt A (fderiv ℝ A (Jproj e P' u)) (Jproj e P' u) ∧
      HasFDerivAt b (fderiv ℝ b (Jproj e P' u)) (Jproj e P' u) ∧
      HasFDerivAt φ (fderiv ℝ φ (Jproj e P' u)) (Jproj e P' u) := by
    intro u hu
    exact ⟨((hA.contDiffAt (hU.mem_nhds hu)).differentiableAt one_ne_zero).hasFDerivAt,
           ((hb.contDiffAt (hU.mem_nhds hu)).differentiableAt one_ne_zero).hasFDerivAt,
           ((hφ.contDiffAt (hU.mem_nhds hu)).differentiableAt one_ne_zero).hasFDerivAt⟩
  set s : Set (Spc e P') := {u | Jproj e P' u ∈ U ∧ (fderiv ℝ (g A b φ) u).det = 0}
    with hsdef
  have hf' : ∀ u ∈ s, HasFDerivWithinAt (g A b φ) (fderiv ℝ (g A b φ) u) s u := by
    intro u hu
    have h := hasFDerivAt_g A b φ u (hdiff u hu.1).1 (hdiff u hu.1).2.1 (hdiff u hu.1).2.2
    rw [h.fderiv]
    exact h.hasFDerivWithinAt
  have hdet' : ∀ u ∈ s, (fderiv ℝ (g A b φ) u).det = 0 := fun u hu => hu.2
  have hSard : (volume : Measure (Spc e P')) ((g A b φ) '' s) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (volume : Measure (Spc e P')) hf' hdet'
  set B : Set (Spc e P') := {q | ∃ x ∈ U, A x + b x q.1.2 + q.1.1 = 0 ∧ φ x = q.2 ∧
      ¬ Function.Injective (fun ξ : Fin (e + 1) → ℝ =>
        (fderiv ℝ φ x ξ, fderiv ℝ (fun z => A z + b z q.1.2) x ξ))} with hBdef
  have hBsub : B ⊆ (g A b φ) '' s := by
    intro q hq
    obtain ⟨x, hxU, hF, hφx, hni⟩ := hq
    set u : Spc e P' := ((Fin.init x, q.1.2), x (Fin.last e)) with hudef
    have hJu : Jproj e P' u = x := by rw [hudef]; exact Fin.snoc_init_self x
    have hWu : Wproj e P' u = q.1.2 := rfl
    obtain ⟨hA', hb', hφ'⟩ := hdiff u (by rw [hJu]; exact hxU)
    have hdetu : (fderiv ℝ (g A b φ) u).det = 0 :=
      det_fderiv_g_eq_zero A b φ u hA' hb' hφ' (by simpa only [hJu, hWu] using hni)
    refine ⟨u, ⟨by rw [hJu]; exact hxU, hdetu⟩, ?_⟩
    have hAx : A x + b x q.1.2 = -q.1.1 := eq_neg_of_add_eq_zero_left hF
    have hgu : g A b φ u = ((-(A x + b x q.1.2), q.1.2), φ x) := by
      rw [hudef]
      simp only [g, Jproj_apply, Wproj_apply, Fin.snoc_init_self]
    rw [hgu, hAx, neg_neg, hφx]
  have hBnull : (volume : Measure (Spc e P')) B = 0 := measure_mono_null hBsub hSard
  have hmain : ∀ᵐ q : Spc e P', (∀ x ∈ U, A x + b x q.1.2 + q.1.1 = 0 → φ x = q.2 →
      Function.Injective (fun ξ : Fin (e + 1) → ℝ =>
        (fderiv ℝ φ x ξ, fderiv ℝ (fun z => A z + b z q.1.2) x ξ))) := by
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ hBnull
    intro q hq
    push_neg at hq
    exact hq
  exact Measure.ae_ae_of_ae_prod hmain

end Work.WilE3.Taylor.CaseII
