import Mathlib
import Submission.Work.Drive.Final.faceEventGates
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Final.halfSquare

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.BoxShrink.Pinch

noncomputable section

/-- The square `(-δ,δ) × (-δ,δ)` shrinks with `δ`. -/
private lemma sq_mono {a b : ℝ} (h : a ≤ b) : sq a ⊆ sq b := by
  intro ξ hξ
  rw [mem_sq] at hξ ⊢
  exact ⟨⟨by linarith [hξ.1.1], by linarith [hξ.1.2, h]⟩,
    ⟨by linarith [hξ.2.1], by linarith [hξ.2.2, h]⟩⟩
private lemma faceKeyLocal {ε s h : ℝ} (hε : ε = 1 ∨ ε = -1) :
    (0 < s - h ∨ 0 < -s - h) ↔ (0 < ε * s - h ∨ 0 < -(ε * s - h) - 2 * h) := by
  rcases hε with h1 | h1
  · rw [h1]
    constructor <;> intro hx <;> rcases hx with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rw [h1]
    constructor <;> intro hx <;> rcases hx with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)

theorem faceEventGatesLocal {ψ : Submission.Diffeo} {K : LeanEval.KnotTheory.PardonDistortion.Knot} {s R : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : LeanEval.KnotTheory.PardonDistortion.R3} {h : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ}
    (hG : Work.Drive.Final.GoodSweepData3 ψ K s c σ u v h R ℓ exc lam0 lam1)
    {p : ℝ × ℝ} (hp : Work.Drive.Final.IsFaceEvent ψ s c σ u v h ℓ p)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ E U₁ U₂ : Set LeanEval.KnotTheory.PardonDistortion.R3,
      Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ) E ∧
      (∃ ε : ℝ, 0 < ε ∧ Metric.ball (Work.BoxShrink.Pinch.par ψ p) ε ∩
          (Work.Drive.EpsSphere.torusOf ψ).carrier ⊆ E) ∧
      E ⊆ Metric.ball (Work.BoxShrink.Pinch.par ψ p) ρ ∧
      (U₁ = ∅ ∨ IsPathConnected U₁) ∧ (U₂ = ∅ ∨ IsPathConnected U₂) ∧
      U₁ ⊆ E ∧ U₂ ⊆ E ∧
      Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ
        (Work.Drive.Final.eventValue ψ ℓ p) ∩ E = U₁ ∪ U₂ := by
  classical
  have hGd : Work.Drive.Final.GoodSweepData ψ K s c σ u v h R ℓ exc lam0 lam1 := hG.1.1
  have hℓne : ℓ ≠ 0 := hGd.1.2.2.1
  have hv1 : ‖v‖ = 1 := hGd.1.2.1
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv1
    norm_num at hv1
  have hh : 0 < h := hGd.1.2.2.2.2.2.1
  have hbox : par ψ p ∈ Submission.PBox s c σ := hp.1
  have hface : |inner ℝ v (par ψ p) - (inner ℝ v c + u)| = h := hp.2.1
  obtain ⟨t, ht⟩ := hp.2.2
  -- At a face event the sweep height is never critical: such a point would be an `IsEvent` of the
  -- sweep (it lies in the box and in the closed slab), and `GoodSweepData3` (through
  -- `GoodSweepData2`) forbids those on the closed slab faces.  Hence the level functional is *not*
  -- critical at a face event and the (non-critical) construction of `faceEventGates` applies
  -- without any non-degeneracy input beyond the bundle.
  have hnotcrit : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0 := by
    intro hcrit
    have hmem : par ψ p ∈ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h :=
      le_of_eq hface
    have hlt : |Work.Drive.Final.slabFn c u v (par ψ p)| < h :=
      hG.1.2.2.2.1 p ⟨hbox, hmem, hcrit⟩
    rw [Work.Drive.Final.slabFn_apply, hface] at hlt
    exact lt_irrefl h hlt
  have htne : t ≠ 0 := by
    intro h0
    exact hnotcrit (by rw [ht, h0, zero_smul])
  have hslabne : fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p ≠ 0 := by
    intro h0
    exact hnotcrit (by rw [ht, h0, smul_zero])
  set a : ℝ := inner ℝ v (par ψ p) - (inner ℝ v c + u) with hadef
  have haface : |a| = h := by rw [hadef]; exact hface
  set ε : ℝ := a / h with hεdef
  have hε : ε = 1 ∨ ε = -1 := by
    rcases (abs_eq (le_of_lt hh)).mp haface with h1 | h1
    · left; rw [hεdef, h1, div_self (ne_of_gt hh)]
    · right; rw [hεdef, h1, neg_div, div_self (ne_of_gt hh)]
  have hεne : ε ≠ 0 := by rcases hε with h1 | h1 <;> rw [h1] <;> norm_num
  have hεsq : ε * ε = 1 := by rcases hε with h1 | h1 <;> rw [h1] <;> norm_num
  have haeq : a = ε * h := by
    rcases (abs_eq (le_of_lt hh)).mp haface with h1 | h1
    · rw [h1]
      have h2 : ε = 1 := by rw [hεdef, h1, div_self (ne_of_gt hh)]
      rw [h2, one_mul]
    · rw [h1]
      have h2 : ε = -1 := by rw [hεdef, h1, neg_div, div_self (ne_of_gt hh)]
      rw [h2]; ring
  set Afun : ℝ × ℝ → ℝ := fun q => ε * Work.Drive.Final.slabFnPar ψ c u v q - h with hAfun
  set Bfun : ℝ × ℝ → ℝ :=
    fun q => Work.Drive.EpsForm.sweepHeight ψ ℓ q - Work.Drive.Final.eventValue ψ ℓ p with hBfun
  have hslab_cont : Continuous (Work.Drive.Final.slabFnPar ψ c u v) := by
    rw [show Work.Drive.Final.slabFnPar ψ c u v
        = fun q : ℝ × ℝ => inner ℝ v (par ψ q) - (inner ℝ v c + u) from rfl]
    exact (continuous_const.inner (par_continuous ψ)).sub continuous_const
  have hslab_sm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.Drive.Final.slabFnPar ψ c u v) p := by
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × ℝ => inner ℝ v (par ψ q)) p :=
      (innerSL ℝ v).contDiff.contDiffAt.comp p (Work.BoxShrink.Pinch.par_contDiff ψ).contDiffAt
    show ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × ℝ => inner ℝ v (par ψ q) - (inner ℝ v c + u)) p
    exact h1.sub (contDiffAt_const (c := inner ℝ v c + u))
  have hslab_diff : DifferentiableAt ℝ (Work.Drive.Final.slabFnPar ψ c u v) p :=
    hslab_sm.differentiableAt (by simp)
  have hAcont : Continuous Afun := by
    rw [hAfun]
    exact (continuous_const.mul hslab_cont).sub continuous_const
  have hAsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Afun p := by
    rw [hAfun]
    exact ((contDiffAt_const (c := ε)).mul hslab_sm).sub (contDiffAt_const (c := h))
  have hBsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Bfun p := by
    rw [hBfun]
    exact ((Work.Smooth.Morse.pullback_contDiff ψ ℓ.contDiff).contDiffAt).sub
      (contDiffAt_const (c := Work.Drive.Final.eventValue ψ ℓ p))
  have hA0 : Afun p = 0 := by
    show ε * Work.Drive.Final.slabFnPar ψ c u v p - h = 0
    have ha : Work.Drive.Final.slabFnPar ψ c u v p = a := by rw [hadef]; rfl
    rw [ha, haeq, ← mul_assoc, hεsq, one_mul, sub_self]
  have hB0 : Bfun p = 0 := by
    show Work.Drive.EpsForm.sweepHeight ψ ℓ p - Work.Drive.Final.eventValue ψ ℓ p = 0
    rw [show Work.Drive.Final.eventValue ψ ℓ p = Work.Drive.EpsForm.sweepHeight ψ ℓ p from rfl,
      sub_self]
  have hBfun_eq : ∀ q : ℝ × ℝ,
      Bfun q = ℓ (par ψ q) - Work.Drive.Final.eventValue ψ ℓ p := by
    intro q
    show Work.Drive.EpsForm.sweepHeight ψ ℓ q - Work.Drive.Final.eventValue ψ ℓ p = _
    rw [show Work.Drive.EpsForm.sweepHeight ψ ℓ q = ℓ (par ψ q) from rfl]
  have hAd : fderiv ℝ Afun p = ε • fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p := by
    rw [hAfun]
    have heq : (fun q : ℝ × ℝ => ε * Work.Drive.Final.slabFnPar ψ c u v q - h)
        = (fun q : ℝ × ℝ => Work.Drive.Final.slabFnPar ψ c u v q * ε - h) := by
      funext q; ring
    rw [heq, fderiv_sub_const, fderiv_mul_const hslab_diff ε]
  have hBd : fderiv ℝ Bfun p = fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p := by
    rw [hBfun, fderiv_sub_const]
  have hAdne : fderiv ℝ Afun p ≠ 0 := by
    rw [hAd]
    exact smul_ne_zero hεne hslabne
  have hrel : fderiv ℝ Bfun p = (t / ε) • fderiv ℝ Afun p := by
    have hslab' : fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p = ε⁻¹ • fderiv ℝ Afun p := by
      rw [hAd, smul_smul, inv_mul_cancel₀ hεne, one_smul]
    rw [hBd, ht, hslab', smul_smul, div_eq_mul_inv]
  -- the linear change of coordinates normalising the active face functional
  obtain ⟨L, hLbij, hLF, hLopen⟩ := exists_linear_normalising (fderiv ℝ Afun p) hAdne
  have hLcomp : (fderiv ℝ Afun p).comp L = ContinuousLinearMap.fst ℝ ℝ ℝ :=
    ContinuousLinearMap.ext fun w => hLF w
  set Vs : ℝ × ℝ → ℝ := Afun ∘ fun ξ : ℝ × ℝ => L ξ + p with hVs
  set Ws : ℝ × ℝ → ℝ := Bfun ∘ fun ξ : ℝ × ℝ => L ξ + p with hWs
  have hshift_cont : Continuous (fun ξ : ℝ × ℝ => L ξ + p) := L.continuous.add_const p
  have hshift_sm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun ξ : ℝ × ℝ => L ξ + p) 0 :=
    (L.contDiff.contDiffAt).add contDiffAt_const
  have hshift_diff : DifferentiableAt ℝ (fun ξ : ℝ × ℝ => L ξ + p) 0 :=
    L.differentiableAt.add_const p
  have hshift_deriv : fderiv ℝ (fun ξ : ℝ × ℝ => L ξ + p) 0 = L := by
    rw [fderiv_add_const, ContinuousLinearMap.fderiv]
  have hmp : (fun ξ : ℝ × ℝ => L ξ + p) 0 = p := by simp
  have hmp' : L (0 : ℝ × ℝ) + p = p := by simp
  have hAsm' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Afun
      ((fun ξ : ℝ × ℝ => L ξ + p) 0) := by
    rw [hmp]; exact hAsm
  have hBsm' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Bfun
      ((fun ξ : ℝ × ℝ => L ξ + p) 0) := by
    rw [hmp]; exact hBsm
  have hA_diff_at : DifferentiableAt ℝ Afun ((fun ξ : ℝ × ℝ => L ξ + p) 0) :=
    hAsm'.differentiableAt (by simp)
  have hB_diff_at : DifferentiableAt ℝ Bfun ((fun ξ : ℝ × ℝ => L ξ + p) 0) :=
    hBsm'.differentiableAt (by simp)
  have hVs0 : Vs 0 = 0 := by
    show Afun (L 0 + p) = 0
    rw [hmp', hA0]
  have hWs0 : Ws 0 = 0 := by
    show Bfun (L 0 + p) = 0
    rw [hmp', hB0]
  have hVssm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Vs 0 := by
    show ContDiffAt ℝ _ (Afun ∘ (fun ξ : ℝ × ℝ => L ξ + p)) 0
    exact hAsm'.comp 0 hshift_sm
  have hWssm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ws 0 := by
    show ContDiffAt ℝ _ (Bfun ∘ (fun ξ : ℝ × ℝ => L ξ + p)) 0
    exact hBsm'.comp 0 hshift_sm
  have hVsd : fderiv ℝ Vs 0 = ContinuousLinearMap.fst ℝ ℝ ℝ := by
    show fderiv ℝ (Afun ∘ (fun ξ : ℝ × ℝ => L ξ + p)) 0 = _
    rw [fderiv_comp 0 hA_diff_at hshift_diff]
    show (fderiv ℝ Afun (L (0 : ℝ × ℝ) + p)).comp
        (fderiv ℝ (fun ξ : ℝ × ℝ => L ξ + p) 0) = _
    rw [hmp', hshift_deriv, hLcomp]
  have hWsd : fderiv ℝ Ws 0 = (t / ε) • ContinuousLinearMap.fst ℝ ℝ ℝ := by
    show fderiv ℝ (Bfun ∘ (fun ξ : ℝ × ℝ => L ξ + p)) 0 = _
    rw [fderiv_comp 0 hB_diff_at hshift_diff]
    show (fderiv ℝ Bfun (L (0 : ℝ × ℝ) + p)).comp
        (fderiv ℝ (fun ξ : ℝ × ℝ => L ξ + p) 0) = _
    rw [hmp', hshift_deriv, hrel]
    rw [ContinuousLinearMap.smul_comp]
    exact congrArg (fun X => (t / ε) • X) hLcomp
  -- path connectedness of the two half-discs
  obtain ⟨δA, hδApos, hδAspec⟩ :=
    halfSquare Vs 1 (by norm_num) hVs0 hVssm (by rw [hVsd, one_smul])
  obtain ⟨δB, hδBpos, hδBspec⟩ :=
    halfSquare Ws (t / ε) (div_ne_zero htne hεne) hWs0 hWssm hWsd
  -- the smallness conditions
  set G : Set (ℝ × ℝ) :=
    (fun q : ℝ × ℝ => par ψ q) ⁻¹' Submission.PBox s c σ ∩
      {q : ℝ × ℝ | -Afun q - 2 * h < 0} with hGdef
  have hGopen : IsOpen G := by
    rw [hGdef]
    exact ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).preimage (par_continuous ψ)).inter
      (isOpen_lt (hAcont.neg.sub continuous_const) continuous_const)
  have hpG : p ∈ G := by
    rw [hGdef]
    refine ⟨hbox, ?_⟩
    show -Afun p - 2 * h < 0
    rw [hA0]
    linarith
  have hpG' : L (0 : ℝ × ℝ) + p ∈ G := by rw [hmp']; exact hpG
  obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ :=
    exists_sq_subset (hshift_cont.continuousAt.preimage_mem_nhds (hGopen.mem_nhds hpG'))
  have hδ₁img : (fun ξ : ℝ × ℝ => L ξ + p) '' sq δ₁ ⊆ G := by
    rintro _ ⟨ξ, hξ, rfl⟩
    exact hδ₁sub hξ
  -- the localisation datum: a square around `p` whose image lies in the ball of radius `ρ`
  have hηcont : Continuous (fun ξ : ℝ × ℝ => par ψ (L ξ + p)) :=
    (par_continuous ψ).comp (L.continuous.add_const p)
  have hη0 : (fun ξ : ℝ × ℝ => par ψ (L ξ + p)) 0 = par ψ p := by
    simp only [ContinuousLinearMap.map_zero, zero_add]
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ := exists_sq_subset
    (hηcont.continuousAt.preimage_mem_nhds (by rw [hmp']; exact Metric.ball_mem_nhds _ hρ))
  have hball_img : ∀ ξ ∈ sq δ₀, par ψ (L ξ + p) ∈ Metric.ball (par ψ p) ρ :=
    fun ξ hξ => hδ₀sub hξ
  set δ : ℝ := min δ₁ (min δA (min δB δ₀)) with hδdef
  have hδpos : 0 < δ := lt_min hδ₁pos (lt_min hδApos (lt_min hδBpos hδ₀pos))
  have hδle₁ : δ ≤ δ₁ := min_le_left _ _
  have hδleA : δ ≤ δA := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδleB : δ ≤ δB :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδle₀ : δ ≤ δ₀ :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hsq_sub : sq δ ⊆ sq δ₁ := sq_mono hδle₁
  set O : Set (ℝ × ℝ) := (fun ξ : ℝ × ℝ => L ξ + p) '' sq δ with hOdef
  have hOG : O ⊆ G := fun _ hq => hδ₁img (Set.image_mono hsq_sub hq)
  have hOopen : IsOpen O := by
    rw [hOdef]
    exact ((isOpenMap_add_right p).comp hLopen) (sq δ) (isOpen_sq δ)
  have hpO : p ∈ O := by
    rw [hOdef]
    refine ⟨0, ?_, by simp⟩
    rw [mem_sq]
    constructor <;> constructor <;> simp only [Prod.fst_zero, Prod.snd_zero] <;>
      linarith [hδpos]
  -- the localisation: the whole linear square lands in the ball of radius `ρ`
  have hEsub : par ψ '' O ⊆ Metric.ball (par ψ p) ρ := by
    rintro y ⟨q, hq, rfl⟩
    rw [hOdef] at hq
    obtain ⟨ξ, hξ, rfl⟩ := hq
    exact hball_img ξ (sq_mono hδle₀ hξ)
  set S₁ : Set (ℝ × ℝ) := sq δ ∩ {ξ : ℝ × ℝ | 0 < Vs ξ} with hS₁def
  set S₂ : Set (ℝ × ℝ) := sq δ ∩ {ξ : ℝ × ℝ | 0 < Ws ξ} with hS₂def
  have hS₁pc : IsPathConnected S₁ := by
    rw [hS₁def]
    exact hδAspec δ hδpos hδleA
  have hS₂pc : IsPathConnected S₂ := by
    rw [hS₂def]
    exact hδBspec δ hδpos hδleB
  have hO1 : O ∩ {q : ℝ × ℝ | 0 < Afun q} = (fun ξ : ℝ × ℝ => L ξ + p) '' S₁ := by
    rw [hOdef, ← Set.image_inter_preimage (fun ξ : ℝ × ℝ => L ξ + p) (sq δ)
      {q : ℝ × ℝ | 0 < Afun q}]
    rfl
  have hO2 : O ∩ {q : ℝ × ℝ | 0 < Bfun q} = (fun ξ : ℝ × ℝ => L ξ + p) '' S₂ := by
    rw [hOdef, ← Set.image_inter_preimage (fun ξ : ℝ × ℝ => L ξ + p) (sq δ)
      {q : ℝ × ℝ | 0 < Bfun q}]
    rfl
  -- the key reformulation of the region condition
  have hkey : ∀ q : ℝ × ℝ,
      (0 < inner ℝ v (par ψ q) - (inner ℝ v c + u) - h ∨
        0 < -(inner ℝ v (par ψ q) - (inner ℝ v c + u)) - h) ↔
      (0 < Afun q ∨ 0 < -Afun q - 2 * h) := by
    intro q
    have hs : Work.Drive.Final.slabFnPar ψ c u v q
        = inner ℝ v (par ψ q) - (inner ℝ v c + u) := rfl
    have h2 := faceKeyLocal (ε := ε) (s := Work.Drive.Final.slabFnPar ψ c u v q) (h := h) hε
    rw [hs] at h2
    have h3 : Afun q = ε * Work.Drive.Final.slabFnPar ψ c u v q - h := by rw [hAfun]
    rw [h3]
    exact h2
  -- the open set of the surface
  have hopenIn : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ)
      (par ψ '' O) := by
    have h' : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ)
        (Work.Smooth.Morse.param ψ '' O) :=
      Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ hOopen
    simpa only [Work.Drive.EpsSphere.torusOf, Work.Smooth.Morse.torus,
      Work.BoxShrink.Pinch.par_def, Work.Smooth.Morse.param_def] using h'
  obtain ⟨W, hWopen, hWeq⟩ := (isOpen_induced_iff.mp hopenIn :
    ∃ W : Set R3, IsOpen W ∧ Subtype.val ⁻¹' W = Subtype.val ⁻¹' (par ψ '' O))
  have hWcarrier : ∀ y : R3, y ∈ (Work.Smooth.Morse.torus ψ).carrier →
      (y ∈ W ↔ y ∈ par ψ '' O) := by
    intro y hy
    have h1 : (⟨y, hy⟩ : (Work.Smooth.Morse.torus ψ).carrier) ∈ Subtype.val ⁻¹' W ↔
        (⟨y, hy⟩ : (Work.Smooth.Morse.torus ψ).carrier) ∈
          Subtype.val ⁻¹' (par ψ '' O) := by
      rw [hWeq]
    rwa [Set.mem_preimage, Set.mem_preimage] at h1
  -- the localised gate set: the carrier trace of the gate, cut down to the ball of radius `ρ`
  set E : Set R3 := W ∩ Metric.ball (par ψ p) ρ with hEdef
  have hEcarrier : ∀ y : R3, y ∈ (Work.Smooth.Morse.torus ψ).carrier →
      (y ∈ E ↔ y ∈ par ψ '' O) := by
    intro y hy
    constructor
    · intro h
      rw [hEdef] at h
      exact (hWcarrier y hy).mp h.1
    · intro h
      rw [hEdef]
      exact ⟨(hWcarrier y hy).mpr h, hEsub h⟩
  have hEball : E ⊆ Metric.ball (par ψ p) ρ := by
    intro y hy
    rw [hEdef] at hy
    exact hy.2
  have hEopenIn : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ) E := by
    have hpre : (Subtype.val ⁻¹' E : Set (Work.Drive.EpsSphere.torusOf ψ).carrier) =
        (Subtype.val ⁻¹' W : Set (Work.Drive.EpsSphere.torusOf ψ).carrier) := by
      ext y
      rw [Set.mem_preimage, Set.mem_preimage]
      constructor
      · intro h
        rw [hEdef] at h
        exact h.1
      · intro h
        rw [hEdef]
        exact ⟨h, hEsub ((hWcarrier y y.2).mp h)⟩
    rw [Work.SurgeryInvariance.IsOpenInCarrier, hpre]
    exact hWopen.preimage continuous_subtype_val
  have hWmem : par ψ p ∈ W :=
    (hWcarrier (par ψ p) (par_mem_carrier ψ p)).mpr ⟨p, hpO, rfl⟩
  have hεrel : ∃ ε : ℝ, 0 < ε ∧ Metric.ball (par ψ p) ε ∩
      (Work.Drive.EpsSphere.torusOf ψ).carrier ⊆ E := by
    obtain ⟨ε₀, hε₀pos, hε₀sub⟩ := Metric.mem_nhds_iff.mp (hWopen.mem_nhds hWmem)
    refine ⟨min ε₀ ρ, lt_min hε₀pos hρ, ?_⟩
    rintro y ⟨hyb, -⟩
    refine ⟨hε₀sub ?_, ?_⟩
    · rw [Metric.mem_ball] at hyb ⊢
      exact lt_of_lt_of_le hyb (min_le_left ε₀ ρ)
    · rw [Metric.mem_ball] at hyb ⊢
      exact lt_of_lt_of_le hyb (min_le_right ε₀ ρ)
  have hU₁pc : par ψ '' (O ∩ {q : ℝ × ℝ | 0 < Afun q}) = ∅ ∨
      IsPathConnected (par ψ '' (O ∩ {q : ℝ × ℝ | 0 < Afun q})) := by
    rw [hO1, Set.image_image]
    exact Or.inr (hS₁pc.image ((par_continuous ψ).comp hshift_cont))
  have hU₂pc : par ψ '' (O ∩ {q : ℝ × ℝ | 0 < Bfun q}) = ∅ ∨
      IsPathConnected (par ψ '' (O ∩ {q : ℝ × ℝ | 0 < Bfun q})) := by
    rw [hO2, Set.image_image]
    exact Or.inr (hS₂pc.image ((par_continuous ψ).comp hshift_cont))
  have hU₁sub : par ψ '' (O ∩ {q : ℝ × ℝ | 0 < Afun q}) ⊆ E := by
    rintro y ⟨q, ⟨hqO, -⟩, rfl⟩
    exact ⟨(hWcarrier (par ψ q) (par_mem_carrier ψ q)).mpr ⟨q, hqO, rfl⟩,
      hEsub ⟨q, hqO, rfl⟩⟩
  have hU₂sub : par ψ '' (O ∩ {q : ℝ × ℝ | 0 < Bfun q}) ⊆ E := by
    rintro y ⟨q, ⟨hqO, -⟩, rfl⟩
    exact ⟨(hWcarrier (par ψ q) (par_mem_carrier ψ q)).mpr ⟨q, hqO, rfl⟩,
      hEsub ⟨q, hqO, rfl⟩⟩
  have hreg : Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ)
      s c σ u v h ℓ (Work.Drive.Final.eventValue ψ ℓ p) ∩ E =
      par ψ '' (O ∩ {q : ℝ × ℝ | 0 < Afun q}) ∪
        par ψ '' (O ∩ {q : ℝ × ℝ | 0 < Bfun q}) := by
    ext y
    constructor
    · rintro ⟨hyreg, hyE⟩
      rw [mem_openTiltedSweepRegion_iff] at hyreg
      obtain ⟨hyc, hybox, hcond⟩ := hyreg
      obtain ⟨q, hqO, hqeq⟩ := (hEcarrier y hyc).mp hyE
      rw [← hqeq] at hcond
      obtain ⟨hqGbox, hqGneg⟩ := hOG hqO
      rcases hcond with h1 | h2 | h3
      · rcases (hkey q).mp (Or.inl h1) with h' | h'
        · exact Or.inl ⟨q, ⟨hqO, h'⟩, hqeq⟩
        · exact absurd h' (not_lt.mpr (le_of_lt hqGneg))
      · rcases (hkey q).mp (Or.inr h2) with h' | h'
        · exact Or.inl ⟨q, ⟨hqO, h'⟩, hqeq⟩
        · exact absurd h' (not_lt.mpr (le_of_lt hqGneg))
      · refine Or.inr ⟨q, ⟨hqO, ?_⟩, hqeq⟩
        show 0 < Bfun q
        rw [hBfun_eq q]
        exact sub_pos.mpr h3
    · rintro (⟨q, ⟨hqO, hA⟩, hqeq⟩ | ⟨q, ⟨hqO, hB⟩, hqeq⟩)
      · refine ⟨?_, ?_⟩
        · rw [← hqeq, mem_openTiltedSweepRegion_iff]
          rcases (hkey q).mpr (Or.inl hA) with h | h
          · exact ⟨par_mem_carrier ψ q, (hOG hqO).1, Or.inl h⟩
          · exact ⟨par_mem_carrier ψ q, (hOG hqO).1, Or.inr (Or.inl h)⟩
        · rw [← hqeq]
          exact (hEcarrier (par ψ q) (par_mem_carrier ψ q)).mpr ⟨q, hqO, rfl⟩
      · refine ⟨?_, ?_⟩
        · rw [← hqeq, mem_openTiltedSweepRegion_iff]
          refine ⟨par_mem_carrier ψ q, (hOG hqO).1, Or.inr (Or.inr ?_)⟩
          have hB' : 0 < Bfun q := hB
          rw [hBfun_eq q] at hB'
          exact sub_pos.mp hB'
        · rw [← hqeq]
          exact (hEcarrier (par ψ q) (par_mem_carrier ψ q)).mpr ⟨q, hqO, rfl⟩

  exact ⟨E, par ψ '' (O ∩ {q : ℝ × ℝ | 0 < Afun q}),
    par ψ '' (O ∩ {q : ℝ × ℝ | 0 < Bfun q}), hEopenIn, hεrel, hEball, hU₁pc, hU₂pc,
    hU₁sub, hU₂sub, hreg⟩

end

end Work.Drive.Final
