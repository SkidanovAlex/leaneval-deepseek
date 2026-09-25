import Mathlib
import Submission.Work.NN.Seeley.Glob
import Submission.Work.NN.Final.leibniz_diff_bound

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Filter
open Work.NN.Final

namespace Work.NN.Seeley

universe u v uY uE uF uG

/-! ### Transport of `gDN` and `gSN` across linear isometry equivalences -/

section Transport

variable {A A' : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup A'] [NormedSpace ℝ A']
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma gDN_comp_lis (e : A ≃ₗᵢ[ℝ] A') (f : Y → A) (i : ℕ) (Ω : Set Y) :
    gDN i (⇑e ∘ f) Ω = gDN i f Ω := by
  unfold gDN
  refine le_antisymm (iSup₂_le fun x hx => ?_) (iSup₂_le fun x hx => ?_)
  · rw [norm_iteratedFDeriv_comp_lis e f x i]
    exact le_iSup₂_of_le x hx le_rfl
  · rw [← norm_iteratedFDeriv_comp_lis e f x i]
    exact le_iSup₂_of_le x hx le_rfl

lemma gSN_comp_lis (e : A ≃ₗᵢ[ℝ] A') (f : Y → A) (i : ℕ) (α : ℝ) (Ω : Set Y) :
    gSN i α (⇑e ∘ f) Ω = gSN i α f Ω := by
  unfold gSN
  refine le_antisymm
    (iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_)
    (iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_)
  · rw [norm_iteratedFDeriv_comp_lis_sub e f x y i]
    exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))
  · rw [← norm_iteratedFDeriv_comp_lis_sub e f x y i]
    exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))

end Transport

/-! ### The bilinear Leibniz bound for `gSN`, with all spaces in one universe -/

section Aux

variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {E F G : Type (max u v)} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma gSN_bilinear_aux (B : E →L[ℝ] F →L[ℝ] G) (i : ℕ) (α : ℝ) {f : Y → E} {g : Y → F}
    {Ω : Set Y} (hf : ContDiff ℝ i f) (hg : ContDiff ℝ i g) :
    gSN i α (fun x => B (f x) (g x)) Ω
      ≤ ENNReal.ofReal ‖B‖ * ∑ j ∈ Finset.range (i + 1), (i.choose j : ENNReal) *
          (gSN j α f Ω * gDN (i - j) g Ω + gDN j f Ω * gSN (i - j) α g Ω) := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  have hd : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  have hCnn : (0 : ℝ) ≤ ‖B‖ := norm_nonneg B
  have hC : ∀ a b, ‖B a b‖ ≤ ‖B‖ * ‖a‖ * ‖b‖ := fun a b => B.le_opNorm₂ a b
  have hpt := bilin_pt i (D := Y) (E := E) (F := F) (G := G) (B := B) (C := ‖B‖) hCnn hC hf hg x y
  have hstep : ‖iteratedFDeriv ℝ i (fun x => B (f x) (g x)) x
        - iteratedFDeriv ℝ i (fun x => B (f x) (g x)) y‖ / ‖x - y‖ ^ α
      ≤ ‖B‖ * ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
          (‖iteratedFDeriv ℝ j f x‖ *
              (‖iteratedFDeriv ℝ (i - j) g x - iteratedFDeriv ℝ (i - j) g y‖ / ‖x - y‖ ^ α)
            + (‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ / ‖x - y‖ ^ α) *
              ‖iteratedFDeriv ℝ (i - j) g y‖) := by
    refine (div_le_div_of_nonneg_right hpt hd).trans (le_of_eq ?_)
    rw [mul_div_assoc]
    congr 1
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj => ?_
    ring
  refine (ENNReal.ofReal_le_ofReal hstep).trans ?_
  rw [ENNReal.ofReal_mul (norm_nonneg B),
      ENNReal.ofReal_sum_of_nonneg (fun j hj => by positivity)]
  gcongr with j hj
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  refine mul_le_mul_right ?_ (i.choose j : ENNReal)
  refine (add_le_add ?_ ?_).trans (le_of_eq (add_comm
    (gDN j f Ω * gSN (i - j) α g Ω) (gSN j α f Ω * gDN (i - j) g Ω)))
  · rw [ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul' (le_gDN j hx) (le_gSN (i - j) α hx hy hxy)
  · rw [ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul' (le_gSN j α hx hy hxy) (le_gDN (i - j) hy)

end Aux

/-! ### The general statement (arbitrary universes), by lifting all spaces to one universe -/

section Main

variable {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type uG} [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma gSN_bilinear_le_univ (B : E →L[ℝ] F →L[ℝ] G) (i : ℕ) (α : ℝ) {f : Y → E} {g : Y → F}
    {Ω : Set Y} (hf : ContDiff ℝ i f) (hg : ContDiff ℝ i g) :
    gSN i α (fun x => B (f x) (g x)) Ω
      ≤ ENNReal.ofReal ‖B‖ * ∑ j ∈ Finset.range (i + 1), (i.choose j : ENNReal) *
          (gSN j α f Ω * gDN (i - j) g Ω + gDN j f Ω * gSN (i - j) α g Ω) := by
  let E' : Type (max uY (max uE (max uF uG))) := ULift.{max uY (max uE (max uF uG)), uE} E
  let F' : Type (max uY (max uE (max uF uG))) := ULift.{max uY (max uE (max uF uG)), uF} F
  let G' : Type (max uY (max uE (max uF uG))) := ULift.{max uY (max uE (max uF uG)), uG} G
  let eE : E ≃ₗᵢ[ℝ] E' := (LinearIsometryEquiv.ulift ℝ E).symm
  let eF : F ≃ₗᵢ[ℝ] F' := (LinearIsometryEquiv.ulift ℝ F).symm
  let eG : G ≃ₗᵢ[ℝ] G' := (LinearIsometryEquiv.ulift ℝ G).symm
  let iE : E' →L[ℝ] E := eE.symm
  let iF : F' →L[ℝ] F := eF.symm
  let jG : G →L[ℝ] G' := eG
  let B' : E' →L[ℝ] F' →L[ℝ] G' :=
    ContinuousLinearMap.compL ℝ E' (F' →L[ℝ] G) (F' →L[ℝ] G')
      (ContinuousLinearMap.compL ℝ F' G G' jG)
      (((B.comp iE).flip.comp iF).flip)
  have hB' : ∀ a' b', B' a' b' = jG (B (iE a') (iF b')) := by
    intro a' b'
    simp only [B', ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_apply]
  have hB'eq : ∀ x, B' (eE (f x)) (eF (g x)) = eG (B (f x) (g x)) := by
    intro x
    rw [hB' (eE (f x)) (eF (g x))]
    have h1 : iE (eE (f x)) = f x := by
      change eE.symm (eE (f x)) = f x
      rw [LinearIsometryEquiv.symm_apply_apply]
    have h2 : iF (eF (g x)) = g x := by
      change eF.symm (eF (g x)) = g x
      rw [LinearIsometryEquiv.symm_apply_apply]
    rw [h1, h2]
    rfl
  have hB'norm : ∀ a' b', ‖B' a' b'‖ ≤ ‖B‖ * ‖a'‖ * ‖b'‖ := by
    intro a' b'
    rw [hB' a' b']
    calc ‖jG (B (iE a') (iF b'))‖ = ‖B (iE a') (iF b')‖ := by
          change ‖eG (B (iE a') (iF b'))‖ = ‖B (iE a') (iF b')‖
          exact LinearIsometryEquiv.norm_map eG _
      _ ≤ ‖B‖ * ‖iE a'‖ * ‖iF b'‖ := B.le_opNorm₂ _ _
      _ = ‖B‖ * ‖a'‖ * ‖b'‖ := by
          rw [show ‖iE a'‖ = ‖a'‖ from by
                change ‖eE.symm a'‖ = ‖a'‖
                exact LinearIsometryEquiv.norm_map eE.symm a',
              show ‖iF b'‖ = ‖b'‖ from by
                change ‖eF.symm b'‖ = ‖b'‖
                exact LinearIsometryEquiv.norm_map eF.symm b']
  have hB'norm_le : ‖B'‖ ≤ ‖B‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B) fun a' => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun b' => ?_
    exact hB'norm a' b'
  have hf' : ContDiff ℝ i (⇑eE ∘ f) := (eE.contDiff).comp hf
  have hg' : ContDiff ℝ i (⇑eF ∘ g) := (eF.contDiff).comp hg
  have hmain : gSN i α (fun x => B' ((⇑eE ∘ f) x) ((⇑eF ∘ g) x)) Ω
      ≤ ENNReal.ofReal ‖B'‖ * ∑ j ∈ Finset.range (i + 1), (i.choose j : ENNReal) *
          (gSN j α (⇑eE ∘ f) Ω * gDN (i - j) (⇑eF ∘ g) Ω
            + gDN j (⇑eE ∘ f) Ω * gSN (i - j) α (⇑eF ∘ g) Ω) :=
    gSN_bilinear_aux (B := B') i α (f := ⇑eE ∘ f) (g := ⇑eF ∘ g) hf' hg'
  have h1 : gSN i α (fun x => B (f x) (g x)) Ω
      = gSN i α (fun x => B' ((⇑eE ∘ f) x) ((⇑eF ∘ g) x)) Ω := by
    rw [← gSN_comp_lis eG (fun x => B (f x) (g x)) i α Ω]
    apply congrArg (fun φ => gSN i α φ Ω)
    funext x
    exact (hB'eq x).symm
  have h2 : gSN i α (fun x => B' ((⇑eE ∘ f) x) ((⇑eF ∘ g) x)) Ω
      ≤ ENNReal.ofReal ‖B‖ * ∑ j ∈ Finset.range (i + 1), (i.choose j : ENNReal) *
          (gSN j α f Ω * gDN (i - j) g Ω + gDN j f Ω * gSN (i - j) α g Ω) := by
    refine hmain.trans ?_
    have hS : (∑ j ∈ Finset.range (i + 1), (i.choose j : ENNReal) *
          (gSN j α (⇑eE ∘ f) Ω * gDN (i - j) (⇑eF ∘ g) Ω
            + gDN j (⇑eE ∘ f) Ω * gSN (i - j) α (⇑eF ∘ g) Ω))
        = (∑ j ∈ Finset.range (i + 1), (i.choose j : ENNReal) *
          (gSN j α f Ω * gDN (i - j) g Ω + gDN j f Ω * gSN (i - j) α g Ω)) := by
      simp only [gSN_comp_lis, gDN_comp_lis]
    rw [hS]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hB'norm_le) _
  exact h1.le.trans h2

end Main

/-- Hölder-seminorm form of the Leibniz bound for a bounded bilinear map applied to two `C^i`
maps, for the global-derivative seminorms `gSN`.  Same proof as
`Work.CR.Flat.Holder.hSN_bilinear_le` (`Submission/Work/CR/Flat/Holder/hSN_bilinear_le.lean`) with
`iteratedFDerivWithin` replaced by `iteratedFDeriv`. -/
theorem gSN_bilinear_le {Y E F G : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (i : ℕ) (α : ℝ) {f : Y → E} {g : Y → F} {Ω : Set Y}
    (hf : ContDiff ℝ i f) (hg : ContDiff ℝ i g) :
    Work.NN.Final.gSN i α (fun x => B (f x) (g x)) Ω
      ≤ ENNReal.ofReal ‖B‖ * ∑ j ∈ Finset.range (i + 1), (i.choose j : ENNReal) *
          (Work.NN.Final.gSN j α f Ω * Work.NN.Final.gDN (i - j) g Ω
            + Work.NN.Final.gDN j f Ω * Work.NN.Final.gSN (i - j) α g Ω) :=
  gSN_bilinear_le_univ B i α hf hg

end Work.NN.Seeley
