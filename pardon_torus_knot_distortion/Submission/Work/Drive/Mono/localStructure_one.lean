import Mathlib
import Submission.Work.Drive.Mono.OneEvBadAux

open LeanEval.KnotTheory.PardonDistortion Set Filter
open scoped RealInnerProductSpace ENNReal Topology

namespace Work.Drive.Mono

noncomputable section

/-! ## Helpers for `localStructure_one` -/

private theorem evLevel_contDiffAt_aux {ψ : Submission.Diffeo} {a₀ b₀ : R3} (ha : ‖a₀‖ = 1)
    (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) {Ψ : ℝ × ℝ → ℝ × ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (hΨ : ContDiffOn ℝ 1 Ψ V) {x : ℝ × ℝ} (hx : x ∈ V) :
    ContDiffAt ℝ 1 (evLevel ψ a₀ b₀ Ψ) x := by
  have hout : ContDiffAt ℝ 1 (Function.uncurry (sH ψ a₀ b₀)) (x.1, Ψ x) :=
    ((contDiff_sH_uncurry ha hb hab ψ).of_le (by norm_num)).contDiffAt
  have hin : ContDiffAt ℝ 1 (fun y : ℝ × ℝ => (y.1, Ψ y)) x :=
    ContDiffAt.prodMk contDiffAt_fst (hΨ.contDiffAt (hV.mem_nhds hx))
  have hmain := hout.comp x hin
  exact hmain.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => rfl)

private theorem isInvertible_of_ne_zero_aux {g : ℝ →L[ℝ] ℝ} (hg : g ≠ 0) : g.IsInvertible := by
  have hg_apply : ∀ x : ℝ, g x = x * g 1 := fun x => by
    simpa [smul_eq_mul] using map_smul g x (1 : ℝ)
  have hg1 : g 1 ≠ 0 := by
    intro h
    apply hg
    apply ContinuousLinearMap.ext
    intro x
    rw [hg_apply x, h, mul_zero]
    simp
  refine ContinuousLinearMap.IsInvertible.of_inverse (f := g)
    (g := ContinuousLinearMap.toSpanSingleton ℝ (g 1)⁻¹) ?_ ?_
  · apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    rw [hg_apply, mul_assoc, inv_mul_cancel₀ hg1, mul_one]
  · apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    rw [hg_apply, mul_assoc, mul_inv_cancel₀ hg1, mul_one]

private theorem cont_wT_aux : Continuous wT := by unfold wT; fun_prop
private theorem cont_wQ_aux : Continuous wQ := by unfold wQ; fun_prop
private theorem cont_wQ'_aux : Continuous wQ' := by unfold wQ'; fun_prop

set_option maxHeartbeats 2000000 in
theorem localStructure_one (ψ : Submission.Diffeo) (v a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0)
    {care : ℝ → ℝ × ℝ → Prop} {τ₀ σ₀ : ℝ} {p₁ p₂ : ℝ × ℝ}
    (K : Work.Drive.Mono.CritChart ψ a₀ b₀ τ₀ p₁) (C : Work.Drive.Mono.EvChart ψ v a₀ b₀ care τ₀ σ₀ p₂)
    (hc : care τ₀ p₂)
    (hlev : Work.Drive.Mono.sH ψ a₀ b₀ τ₀ p₁ = Work.Drive.Mono.sH ψ a₀ b₀ τ₀ p₂)
    {η u₀ h₀ : ℝ} (hη : η = 1 ∨ η = -1)
    (hu : Work.Drive.Mono.hFn ψ v p₂ = (inner ℝ v c + u₀) + η * h₀)
    (hint : |Work.Drive.Mono.hFn ψ v p₁ - (inner ℝ v c + u₀)| < h₀) :
    ∃ (O : Set Work.Drive.Mono.Wit) (V : Set (ℝ × ℝ)) (φ : ℝ × ℝ → Work.Drive.Mono.Wit),
      IsOpen O ∧ Work.Drive.Mono.wit u₀ h₀ τ₀ p₁ p₂ ∈ O ∧ IsOpen V ∧ (τ₀, u₀) ∈ V ∧
      ContDiffOn ℝ 1 φ V ∧
      {w : Work.Drive.Mono.Wit | fderiv ℝ (fun x : ℝ × ℝ => Work.Drive.Mono.sH ψ a₀ b₀ (Work.Drive.Mono.wT w) x) (Work.Drive.Mono.wQ w) = 0 ∧
          Work.Drive.Mono.wQ w ∈ K.U ∧ |Work.Drive.Mono.hFn ψ v (Work.Drive.Mono.wQ w) - (inner ℝ v c + Work.Drive.Mono.wU w)| < Work.Drive.Mono.wH w ∧
          care (Work.Drive.Mono.wT w) (Work.Drive.Mono.wQ' w) ∧
          Work.Drive.Mono.hFn ψ v (Work.Drive.Mono.wQ' w) = (inner ℝ v c + Work.Drive.Mono.wU w) + η * Work.Drive.Mono.wH w ∧
          Work.Drive.Mono.sH ψ a₀ b₀ (Work.Drive.Mono.wT w) (Work.Drive.Mono.wQ w) = Work.Drive.Mono.sH ψ a₀ b₀ (Work.Drive.Mono.wT w) (Work.Drive.Mono.wQ' w)} ∩ O ⊆ φ '' V := by
  classical
  -- (0) the slab coordinate of `p₂`
  have hσ₀ : σ₀ = hFn ψ v p₂ := by
    have h1 : hFn ψ v (C.Ψ (τ₀, σ₀)) = σ₀ := C.hg (τ₀, σ₀) C.hVmem
    rw [C.hΨmem] at h1
    exact h1.symm
  -- (1) the level of the critical branch
  let L : ℝ → ℝ := fun τ => sH ψ a₀ b₀ τ (K.P τ)
  have hLcd : ContDiffAt ℝ 1 L τ₀ := by
    have huniv : ContDiffAt ℝ 1 (Function.uncurry (sH ψ a₀ b₀)) (τ₀, K.P τ₀) :=
      ((contDiff_sH_uncurry ha hb hab ψ).of_le (by norm_num)).contDiffAt
    have hPcd : ContDiffAt ℝ 1 K.P τ₀ := K.hPcd.contDiffAt (K.hVopen.mem_nhds K.hVmem)
    have hpair : ContDiffAt ℝ 1 (fun τ : ℝ => (τ, K.P τ)) τ₀ := contDiffAt_id.prodMk hPcd
    have h := huniv.comp τ₀ hpair
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => rfl)
  -- (2) the implicit equation `f`
  let f : ℝ × ℝ → ℝ := fun x => evLevel ψ a₀ b₀ C.Ψ x - L x.1
  have hEvcd : ContDiffAt ℝ 1 (evLevel ψ a₀ b₀ C.Ψ) (τ₀, σ₀) :=
    evLevel_contDiffAt_aux ha hb hab C.hVopen C.hΨcd C.hVmem
  have hcompL : ContDiffAt ℝ 1 (fun x : ℝ × ℝ => L x.1) (τ₀, σ₀) := by
    have h : ContDiffAt ℝ 1 (L ∘ (Prod.fst : ℝ × ℝ → ℝ)) (τ₀, σ₀) :=
      hLcd.comp (τ₀, σ₀) contDiffAt_fst
    simpa [Function.comp_def] using h
  have hfcd : ContDiffAt ℝ 1 f (τ₀, σ₀) := hEvcd.sub hcompL
  have hf0 : f (τ₀, σ₀) = 0 := by
    have hff : f (τ₀, σ₀) = sH ψ a₀ b₀ τ₀ (C.Ψ (τ₀, σ₀)) - sH ψ a₀ b₀ τ₀ (K.P τ₀) := rfl
    rw [hff, C.hΨmem, K.hPmem, hlev, sub_self]
  -- (3) the `σ`-derivative of `f` does not vanish
  have hσne : (fderiv ℝ (evLevel ψ a₀ b₀ C.Ψ) (τ₀, σ₀)) (0, 1) ≠ 0 := by
    have h := C.hσ
    rwa [fderivWithin_of_isOpen C.hVopen C.hVmem] at h
  have hfderiv : fderiv ℝ f (τ₀, σ₀)
      = fderiv ℝ (evLevel ψ a₀ b₀ C.Ψ) (τ₀, σ₀)
        - ((fderiv ℝ L τ₀) ∘SL ContinuousLinearMap.fst ℝ ℝ ℝ) := by
    have h1 : HasFDerivAt (evLevel ψ a₀ b₀ C.Ψ)
        (fderiv ℝ (evLevel ψ a₀ b₀ C.Ψ) (τ₀, σ₀)) (τ₀, σ₀) :=
      (hEvcd.differentiableAt (by norm_num)).hasFDerivAt
    have h2 : HasFDerivAt (fun x : ℝ × ℝ => L x.1)
        ((fderiv ℝ L τ₀) ∘SL ContinuousLinearMap.fst ℝ ℝ ℝ) (τ₀, σ₀) := by
      have hL' : HasFDerivAt L (fderiv ℝ L τ₀) τ₀ :=
        (hLcd.differentiableAt (by norm_num)).hasFDerivAt
      have h4 : HasFDerivAt (L ∘ (Prod.fst : ℝ × ℝ → ℝ))
          ((fderiv ℝ L τ₀) ∘SL ContinuousLinearMap.fst ℝ ℝ ℝ) (τ₀, σ₀) :=
        HasFDerivAt.comp (τ₀, σ₀) hL'
          (hasFDerivAt_fst : HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ)
            (ContinuousLinearMap.fst ℝ ℝ ℝ) (τ₀, σ₀))
      simpa [Function.comp_def] using h4
    exact (h1.sub h2).fderiv
  have hfderiv_app : (fderiv ℝ f (τ₀, σ₀)) (0, 1)
      = (fderiv ℝ (evLevel ψ a₀ b₀ C.Ψ) (τ₀, σ₀)) (0, 1) := by
    rw [hfderiv]
    have hz : ((fderiv ℝ L τ₀) ∘SL ContinuousLinearMap.fst ℝ ℝ ℝ) (0, 1) = 0 := by
      rw [ContinuousLinearMap.comp_apply]
      exact map_zero _
    rw [ContinuousLinearMap.sub_apply, hz, sub_zero]
  have hne : ((fderiv ℝ f (τ₀, σ₀)) ∘SL ContinuousLinearMap.inr ℝ ℝ ℝ) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun T : ℝ →L[ℝ] ℝ => T 1) h0
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
      ContinuousLinearMap.inr_apply] at h1
    rw [hfderiv_app] at h1
    exact hσne h1
  -- (4) the implicit function
  have hinv : ((fderiv ℝ f (τ₀, σ₀)) ∘SL ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible :=
    isInvertible_of_ne_zero_aux hne
  let S : ℝ → ℝ := hfcd.implicitFunction (by norm_num) hinv
  have hScd : ContDiffAt ℝ 1 S τ₀ := hfcd.contDiffAt_implicitFunction (by norm_num) hinv
  have hSself : S τ₀ = σ₀ := hfcd.implicitFunction_apply_self (by norm_num) hinv
  have hSiff : ∀ᶠ x : ℝ × ℝ in 𝓝 (τ₀, σ₀),
      f x = f (τ₀, σ₀) ↔ S x.1 = x.2 :=
    hfcd.eventually_apply_eq_iff_implicitFunction (by norm_num) hinv
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hSiff
  have hiff : ∀ x : ℝ × ℝ, dist x (τ₀, σ₀) < ε → (f x = f (τ₀, σ₀) ↔ S x.1 = x.2) :=
    fun x hx => hball (Metric.mem_ball.mpr hx)
  -- (5) an open set of tilts on which everything is defined
  have hScdOn_ex : ∃ W ∈ 𝓝 τ₀, ContDiffOn ℝ 1 S W := by
    have h := (contDiffWithinAt_iff_contDiffOn_nhds (𝕜 := ℝ) (f := S) (s := Set.univ)
      (x := τ₀) (n := 1) (by norm_num)).mp hScd
    simpa using h
  obtain ⟨W₀, hW₀mem, hW₀cd⟩ := hScdOn_ex
  obtain ⟨Wa, hWa_sub, hWa_open, hWa_mem⟩ := mem_nhds_iff.mp hW₀mem
  have hWacd : ContDiffOn ℝ 1 S Wa := hW₀cd.mono hWa_sub
  have hScont : ContinuousAt S τ₀ := (hScd.differentiableAt (by norm_num)).continuousAt
  have hpaircont : ContinuousAt (fun τ : ℝ => (τ, S τ)) τ₀ :=
    ContinuousAt.prodMk continuousAt_id hScont
  have hk : (fun τ : ℝ => (τ, S τ)) ⁻¹' C.V ∈ 𝓝 τ₀ := by
    refine hpaircont.preimage_mem_nhds (C.hVopen.mem_nhds ?_)
    rw [hSself]
    exact C.hVmem
  have hKV : K.V ∈ 𝓝 τ₀ := K.hVopen.mem_nhds K.hVmem
  have hWmem₀ : Wa ∩ K.V ∩ ((fun τ : ℝ => (τ, S τ)) ⁻¹' C.V) ∈ 𝓝 τ₀ :=
    Filter.inter_mem (Filter.inter_mem (hWa_open.mem_nhds hWa_mem) hKV) hk
  obtain ⟨W, hWsub, hWopen, hWmem⟩ := mem_nhds_iff.mp hWmem₀
  have hWcd : ContDiffOn ℝ 1 S W := hWacd.mono (fun τ hτ => (hWsub hτ).1.1)
  have hWK : ∀ τ ∈ W, τ ∈ K.V := fun τ hτ => (hWsub hτ).1.2
  have hWCV : ∀ τ ∈ W, (τ, S τ) ∈ C.V := fun τ hτ => (hWsub hτ).2
  -- (6) the parameter domain
  let V : Set (ℝ × ℝ) := W ×ˢ Set.univ
  have hVopen : IsOpen V := hWopen.prod isOpen_univ
  have hVmem : (τ₀, u₀) ∈ V := ⟨hWmem, trivial⟩
  -- (7) the parametrisation
  let φ : ℝ × ℝ → Wit :=
    fun y => wit y.2 (η * (S y.1 - inner ℝ v c - y.2)) y.1 (K.P y.1) (C.Ψ (y.1, S y.1))
  have hScomp : ContDiffOn ℝ 1 (fun y : ℝ × ℝ => S y.1) V :=
    hWcd.comp contDiff_fst.contDiffOn (fun y hy => hy.1)
  have hfstcd : ContDiffOn ℝ 1 (fun y : ℝ × ℝ => y.1) V := contDiff_fst.contDiffOn
  have hsndcd : ContDiffOn ℝ 1 (fun y : ℝ × ℝ => y.2) V := contDiff_snd.contDiffOn
  have hKPcd : ContDiffOn ℝ 1 (fun y : ℝ × ℝ => K.P y.1) V :=
    K.hPcd.comp contDiff_fst.contDiffOn (fun y hy => hWK y.1 hy.1)
  have hΨcd : ContDiffOn ℝ 1 (fun y : ℝ × ℝ => C.Ψ (y.1, S y.1)) V :=
    C.hΨcd.comp (contDiff_fst.contDiffOn.prodMk hScomp) (fun y hy => hWCV y.1 hy.1)
  have hφcd : ContDiffOn ℝ 1 φ V := by
    have hmain : ContDiffOn ℝ 1 (fun y : ℝ × ℝ =>
        (y.2, (η * (S y.1 - inner ℝ v c - y.2), (y.1, (K.P y.1, C.Ψ (y.1, S y.1)))))) V :=
      hsndcd.prodMk ((contDiffOn_const.mul ((hScomp.sub contDiffOn_const).sub hsndcd)).prodMk
        (hfstcd.prodMk (hKPcd.prodMk hΨcd)))
    exact hmain
  -- (8) the witness neighbourhood
  let O : Set Wit :=
    (wQ ⁻¹' K.U) ∩ (wT ⁻¹' K.V) ∩ (wQ' ⁻¹' C.U) ∩
    ((fun w : Wit => (wT w, hFn ψ v (wQ' w))) ⁻¹' C.V) ∩
    {w : Wit | dist (wT w, hFn ψ v (wQ' w)) (τ₀, σ₀) < ε} ∩
    (wT ⁻¹' W)
  have hOopen : IsOpen O := by
    have hcont₂ : Continuous (fun w : Wit => (wT w, hFn ψ v (wQ' w))) :=
      cont_wT_aux.prodMk ((contDiff_hFn ψ v).continuous.comp cont_wQ'_aux)
    have hcontD : Continuous (fun w : Wit => dist (wT w, hFn ψ v (wQ' w)) (τ₀, σ₀)) :=
      continuous_dist.comp (hcont₂.prodMk continuous_const)
    exact (((((K.hUopen.preimage cont_wQ_aux).inter (K.hVopen.preimage cont_wT_aux)).inter
      (C.hUopen.preimage cont_wQ'_aux)).inter (C.hVopen.preimage hcont₂)).inter
      (isOpen_Iio.preimage hcontD)).inter (hWopen.preimage cont_wT_aux)
  have hwit_mem : wit u₀ h₀ τ₀ p₁ p₂ ∈ O := by
    have hpair : ((τ₀, hFn ψ v p₂) : ℝ × ℝ) = (τ₀, σ₀) := by rw [hσ₀]
    refine ⟨⟨⟨⟨⟨K.hUmem, K.hVmem⟩, C.hUmem⟩, ?_⟩, ?_⟩, hWmem⟩
    · show (τ₀, hFn ψ v p₂) ∈ C.V
      rw [hpair]
      exact C.hVmem
    · show dist (τ₀, hFn ψ v p₂) (τ₀, σ₀) < ε
      rw [hpair, dist_self]
      exact hε
  -- (9) the inclusion
  refine ⟨O, V, φ, hOopen, hwit_mem, hVopen, hVmem, hφcd, ?_⟩
  intro w hw
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hw
  obtain ⟨⟨hcrit, hQmem, hineq, hcare, hhFn', hlev'⟩, hwO⟩ := hw
  have hwO' : w ∈ ((wQ ⁻¹' K.U) ∩ (wT ⁻¹' K.V) ∩ (wQ' ⁻¹' C.U) ∩
      ((fun w : Wit => (wT w, hFn ψ v (wQ' w))) ⁻¹' C.V) ∩
      {w : Wit | dist (wT w, hFn ψ v (wQ' w)) (τ₀, σ₀) < ε} ∩
      (wT ⁻¹' W)) := hwO
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage] at hwO'
  obtain ⟨⟨⟨⟨⟨hQmem', hTV⟩, hQ'mem'⟩, hCV⟩, hdist⟩, hWV⟩ := hwO'
  have hq : wQ w = K.P (wT w) := K.huniq (wT w) hTV (wQ w) hQmem' hcrit
  have hq' : wQ' w = C.Ψ (wT w, hFn ψ v (wQ' w)) :=
    C.huniq (wT w) (hFn ψ v (wQ' w)) (wQ' w) hCV hQ'mem' hcare rfl
  have hfval : f (wT w, hFn ψ v (wQ' w)) = f (τ₀, σ₀) := by
    have h1 : f (wT w, hFn ψ v (wQ' w))
        = sH ψ a₀ b₀ (wT w) (C.Ψ (wT w, hFn ψ v (wQ' w)))
          - sH ψ a₀ b₀ (wT w) (K.P (wT w)) := rfl
    rw [h1, ← hq', ← hq, hlev', sub_self, hf0]
  have hSet : S (wT w) = hFn ψ v (wQ' w) :=
    (hiff (wT w, hFn ψ v (wQ' w)) hdist).mp hfval
  have hηsq : η * η = 1 := by rcases hη with h | h <;> rw [h] <;> norm_num
  have hhu : η * (S (wT w) - inner ℝ v c - wU w) = wH w := by
    rw [hSet]
    calc η * (hFn ψ v (wQ' w) - inner ℝ v c - wU w)
        = η * (η * wH w) := by rw [hhFn']; ring
      _ = wH w := by rw [← mul_assoc, hηsq, one_mul]
  have hφval : φ (wT w, wU w) = w := by
    have hφ1 : φ (wT w, wU w)
        = wit (wU w) (η * (S (wT w) - inner ℝ v c - wU w)) (wT w) (K.P (wT w))
            (C.Ψ (wT w, S (wT w))) := rfl
    rw [hφ1, hhu, hSet, ← hq, ← hq']
    obtain ⟨uu, hh, tt, qq, qq'⟩ := w
    rfl
  exact ⟨(wT w, wU w), ⟨hWV, trivial⟩, hφval⟩

end

end Work.Drive.Mono
