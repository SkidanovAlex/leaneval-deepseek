import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalBasis.Defs
import Submission.Work.FTS.GalBasis.c0_pos
import Submission.Work.FTS.GalBasis.cc_closure
import Submission.Work.FTS.GalBasis.Gfar_basic
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.GalBasis.cc.CutDefs
import Submission.Work.FTS.GalBasis.cc.CutSpec
import Submission.Work.FTS.GalBasis.cc.SlotDefs
import Submission.Work.FTS.GalBasis.cc.ShrinkDefs
import Submission.Work.FTS.GalBasis.cc.HkSq_sub_psiCut_tendsto
import Submission.Work.FTS.GalBasis.cc.abs_L12_le_HkNorm
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.GalLimit.Closure.phi_HQo
import Submission.Work.FTS.LocData.HkSq_const_mul
import Submission.Work.FTS.LocData.L12_add_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis

open Work.FTS.Galerkin (Fn)

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Auxiliary facts: extensionality of the `ℋ⁴`-objects and of `L₁₂` -/

/-- Pointwise-equal functions have the same `D_z`-iterates. -/
theorem DzIter_congr_all {a b : Fn} (h : ∀ z θ, a z θ = b z θ) (n : ℕ) :
    ∀ z θ, Work.Spaces.DzIter n a z θ = Work.Spaces.DzIter n b z θ := by
  induction n with
  | zero => exact h
  | succ n ih =>
      intro z θ
      rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.Dz,
        Work.Spaces.pz, Work.Spaces.pz]
      have heq : (fun z' => Work.Spaces.DzIter n a z' θ)
          = (fun z' => Work.Spaces.DzIter n b z' θ) := funext fun z' => ih z' θ
      rw [heq]

/-- Pointwise-equal functions have the same `D_θ`-iterates. -/
theorem DthIter_congr_all {a b : Fn} (h : ∀ z θ, a z θ = b z θ) (n : ℕ) :
    ∀ z θ, Work.Spaces.DthIter n a z θ = Work.Spaces.DthIter n b z θ := by
  induction n with
  | zero => exact h
  | succ n ih =>
      intro z θ
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.Dth,
        Work.Spaces.pth, Work.Spaces.pth]
      have heq : (fun θ' => Work.Spaces.DthIter n a z θ')
          = (fun θ' => Work.Spaces.DthIter n b z θ') := funext fun θ' => ih z θ'
      rw [heq]

/-- Pointwise-equal functions have the same mixed iterates. -/
theorem mixed_congr_all {a b : Fn} (h : ∀ z θ, a z θ = b z θ) (j i : ℕ) :
    ∀ z θ, Work.Spaces.mixed j i a z θ = Work.Spaces.mixed j i b z θ := by
  intro z θ
  exact DzIter_congr_all (DthIter_congr_all h i) j z θ

/-- Pointwise-equal functions have the same `ℋ^k`-integrand. -/
theorem HkIntegrand_congr_all {a b : Fn} (h : ∀ z θ, a z θ = b z θ) (α : ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k a z θ = Work.Spaces.HkIntegrand α k b z θ := by
  have hz : ∀ i : ℕ, Work.Spaces.DzIter i a z θ = Work.Spaces.DzIter i b z θ :=
    fun i => DzIter_congr_all h i z θ
  have hm : ∀ j i : ℕ, Work.Spaces.mixed j i a z θ = Work.Spaces.mixed j i b z θ :=
    fun j i => mixed_congr_all h j i z θ
  simp only [Work.Spaces.HkIntegrand, hz, hm]

/-- Pointwise-equal functions have the same `ℋ^k`-square. -/
theorem HkSq_congr_all {a b : Fn} (h : ∀ z θ, a z θ = b z θ) (α : ℝ) (k : ℕ) :
    Work.Spaces.HkSq α k a = Work.Spaces.HkSq α k b := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => HkIntegrand_congr_all h α k z θ)

/-- Pointwise-equal functions have the same `ℋ^k`-norm. -/
theorem HkNorm_congr_all {a b : Fn} (h : ∀ z θ, a z θ = b z θ) (α : ℝ) (k : ℕ) :
    Work.Spaces.HkNorm α k a = Work.Spaces.HkNorm α k b := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, HkSq_congr_all h α k]

/-- Pointwise-equal functions have the same `ℋ^k`-membership. -/
theorem HkMem_congr_all {a b : Fn} (h : ∀ z θ, a z θ = b z θ) (α : ℝ) (k : ℕ)
    (hm : Work.Spaces.HkMem α k a) : Work.Spaces.HkMem α k b := by
  have hpt : ∀ z θ, Work.Spaces.HkIntegrand α k a z θ = Work.Spaces.HkIntegrand α k b z θ :=
    fun z θ => HkIntegrand_congr_all h α k z θ
  constructor
  · intro z hz
    exact (hm.1 z hz).congr_fun (fun θ _ => hpt z θ) measurableSet_Icc
  · have h2 : (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k a z θ)
        = (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k b z θ) := by
      funext z
      exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => hpt z θ)
    rw [← h2]
    exact hm.2

/-- `L₁₂` only depends on the pointwise values. -/
theorem L12_congr_all {a b : Fn} (h : ∀ z θ, a z θ = b z θ) :
    ∀ z, Work.Construction.L12 a z = Work.Construction.L12 b z := by
  intro z
  simp only [Work.Construction.L12, Work.FM.L12]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
  simp only [Work.FM.L12dens]
  exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by rw [h s θ])

/-- `L₁₂` is homogeneous. -/
theorem L12_const_mul (c : ℝ) (a : Fn) :
    ∀ z, Work.Construction.L12 (fun z θ => c * a z θ) z = c * Work.Construction.L12 a z := by
  intro z
  simp only [Work.Construction.L12, Work.FM.L12]
  have hpt : (fun s => Work.FM.L12dens Work.Spaces.K (fun z θ => c * a z θ) s)
      = fun s => c * Work.FM.L12dens Work.Spaces.K a s :=
    funext fun s => Work.FTS.LocData.L12dens_const_mul Work.Spaces.K c a s
  rw [hpt, MeasureTheory.integral_const_mul]

/-- `HkSq` is nonnegative. -/
theorem HkSq_nonneg' (α : ℝ) (k : ℕ) (g : Fn) : 0 ≤ Work.Spaces.HkSq α k g := by
  rw [Work.Spaces.HkSq]
  exact setIntegral_nonneg measurableSet_Ici fun z _ =>
    setIntegral_nonneg measurableSet_Icc fun θ _ => Work.Spaces.HkIntegrand_nonneg α k g z θ

/-- `Ccφ` from global smoothness and a support box. -/
theorem Ccφ_of_contDiff_supp {g : Fn} {a' b' δ' : ℝ} (ha' : 0 < a') (hab' : a' < b')
    (hδ' : 0 < δ') (hδ'π : δ' < Real.pi / 2 - δ')
    (hc : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry g)) (hs : SuppIn g a' b' δ') : Ccφ g := by
  have hb' : 0 < b' := lt_trans ha' hab'
  refine ⟨a' / 2, 2 * b', δ' / 2, by positivity, by linarith, by positivity,
    by linarith, hc, a', b', δ', by linarith, hab', by linarith,
    by linarith, hδ'π, hs⟩

/-- `HkMem` is closed under multiplication by a constant. -/
theorem HkMem_const_mul_all {α : ℝ} {k : ℕ} (c : ℝ) {g : Fn}
    (hm : Work.Spaces.HkMem α k g) : Work.Spaces.HkMem α k (fun z θ => c * g z θ) := by
  constructor
  · intro z hz
    rw [funext fun θ => Work.FTS.LocData.HkIntegrand_const_mul α k c g z θ]
    exact (hm.1 z hz).const_mul (c ^ 2)
  · have h2 : (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => c * g z θ) z θ)
        = fun z => c ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ := by
      funext z
      rw [funext fun θ => Work.FTS.LocData.HkIntegrand_const_mul α k c g z θ,
        MeasureTheory.integral_const_mul]
    rw [h2]
    exact hm.2.const_mul (c ^ 2)

/-- `SmoothOpen` is closed under subtraction. -/
theorem smoothOpen_sub_all {a b : Fn} (ha : Work.FTS.EllipticEst.SmoothOpen a)
    (hb : Work.FTS.EllipticEst.SmoothOpen b) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => a z θ - b z θ) := by
  have hfun : (fun z θ => a z θ - b z θ) = (fun z θ => a z θ + -b z θ) := by
    funext z θ; ring
  rw [hfun]
  exact Work.FTS.EllipticEst.smoothOpen_add ha (smoothOpen_neg hb)


/-- The product of the cutoff with a function that is smooth on the open quadrant is globally
`C^∞`: the cutoff vanishes off a box contained in the open quadrant. -/
theorem contDiff_psiCut_mul {ψ : ℕ → Fn} {K : ℝ} (hs : cc.CutSpec ψ K) (N : ℕ) {f : Fn}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (fun z θ => ψ N z θ * f z θ)) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨z, θ⟩
  by_cases hbox : z ∈ Set.Icc (cc.zlo N) (cc.zhi N) ∧ θ ∈ Set.Icc (cc.tlo N) (cc.thi N)
  · obtain ⟨hz, hθ⟩ := hbox
    obtain ⟨hz0, hθ0, hθ2⟩ := cc.box_subset_quadrant N hz hθ
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (Function.uncurry (ψ N)) (z, θ) := (hs.smooth N).contDiffAt
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (Function.uncurry f) (z, θ) :=
      hf.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz0, hθ0, hθ2⟩))
    have h3 : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun p : ℝ × ℝ => ψ N p.1 p.2 * f p.1 p.2) (z, θ) := h1.mul h2
    exact h3
  · have hev : (fun p : ℝ × ℝ => ψ N p.1 p.2 * f p.1 p.2) =ᶠ[𝓝 (z, θ)] (fun _ => (0 : ℝ)) := by
      have hopen : ∀ᶠ p : ℝ × ℝ in 𝓝 (z, θ),
          p.1 ∉ Set.Icc (cc.zlo N) (cc.zhi N) ∨ p.2 ∉ Set.Icc (cc.tlo N) (cc.thi N) := by
        rcases not_and_or.mp hbox with hz | hθ
        · have hset : {p : ℝ × ℝ | p.1 ∉ Set.Icc (cc.zlo N) (cc.zhi N)} ∈ 𝓝 (z, θ) := by
            have h1 : IsOpen {p : ℝ × ℝ | p.1 ∉ Set.Icc (cc.zlo N) (cc.zhi N)} :=
              isClosed_Icc.isOpen_compl.preimage continuous_fst
            exact h1.mem_nhds hz
          filter_upwards [hset] with p hp
          exact Or.inl hp
        · have hset : {p : ℝ × ℝ | p.2 ∉ Set.Icc (cc.tlo N) (cc.thi N)} ∈ 𝓝 (z, θ) := by
            have h1 : IsOpen {p : ℝ × ℝ | p.2 ∉ Set.Icc (cc.tlo N) (cc.thi N)} :=
              isClosed_Icc.isOpen_compl.preimage continuous_snd
            exact h1.mem_nhds hθ
          filter_upwards [hset] with p hp
          exact Or.inr hp
      filter_upwards [hopen] with p hp
      exact mul_eq_zero_of_left (hs.zero N p.1 p.2 hp) _
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev

theorem zlo_pos (N : ℕ) : 0 < cc.zlo N := by simp only [cc.zlo]; positivity
theorem tlo_pos (N : ℕ) : 0 < cc.tlo N := by simp only [cc.tlo]; positivity
theorem zlo_lt_zhi (N : ℕ) : cc.zlo N < cc.zhi N := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  simp only [cc.zlo, cc.zhi]
  rw [div_lt_iff₀ hN]
  nlinarith [sq_nonneg ((N : ℝ) + 1)]

theorem exists_cc_of_honClass {α : ℝ} (hα : 0 < α) {f : Work.FTS.Galerkin.Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hb : Work.FTS.Nonlin.BdryTraces α 4 f) (hl : Work.Construction.L12 f 0 = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Work.FTS.Galerkin.Fn, Coreφ g ∧
      Work.Spaces.HkNorm α 4 (fun z θ => f z θ - g z θ) < ε := by
  classical
  -- ## 1. the cutoff family, the `L₁₂`-bound and the far bump
  obtain ⟨ψ, K, hs⟩ := cc.exists_cutSpec
  obtain ⟨C12, hC12pos, hC12⟩ := cc.abs_L12_le_HkNorm
  have hc0pos : 0 < c0 := c0_pos
  have hc0ne : c0 ≠ 0 := ne_of_gt hc0pos
  obtain ⟨hGfar_cc, hGfar_nn, hGfar_supp⟩ := Gfar_basic
  have hGfar_ct : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Gfar) := hGfar_cc.contDiff
  have hGfar_sm : Work.FTS.EllipticEst.SmoothOpen Gfar :=
    Work.FTS.GalLimit.Closure.smoothOpen_of_contDiff hGfar_ct
  have hGfar_suppbox : ∀ z θ : ℝ,
      (z ∉ Set.Icc (10 : ℝ) 20 ∨ θ ∉ Set.Icc (1 / 4 : ℝ) (Real.pi / 2 - 1 / 4)) →
        Gfar z θ = 0 := by
    intro z θ h
    refine hGfar_supp z θ ?_
    have hπ : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
    rcases h with hz | hθ
    · have hz' : z < 10 ∨ 20 < z := by
        by_contra hc
        push_neg at hc
        exact hz ⟨hc.1, hc.2⟩
      rcases hz' with h1 | h1
      · exact Or.inl (le_of_lt h1)
      · exact Or.inr (Or.inl (le_of_lt h1))
    · have hθ' : θ < 1 / 4 ∨ Real.pi / 2 - 1 / 4 < θ := by
        by_contra hc
        push_neg at hc
        exact hθ ⟨hc.1, hc.2⟩
      rcases hθ' with h1 | h1
      · exact Or.inr (Or.inr (Or.inl (le_of_lt h1)))
      · exact Or.inr (Or.inr (Or.inr (by linarith)))
  have hGfar_mem : Work.Spaces.HkMem α 4 Gfar :=
    Work.FTS.GalLimit.Closure.hkMem_of_suppIn α 4 (by norm_num) (by norm_num) (by norm_num)
      (Work.FTS.GalLimit.Closure.smoothQuad_of_contDiff hGfar_ct) hGfar_suppbox
  -- ## 2. the `ε`-budget
  set A : ℝ := Work.Spaces.HkSq α 4 Gfar with hAdef
  set δ : ℝ := ε ^ 2 / (4 * (1 + C12 ^ 2 * A / c0 ^ 2)) with hδdef
  have hA0 : 0 ≤ A := HkSq_nonneg' α 4 Gfar
  have hδpos : 0 < δ := by
    rw [hδdef]
    have hq : 0 ≤ C12 ^ 2 * A / c0 ^ 2 := by positivity
    positivity
  -- ## 3. the cutoff index and the error
  obtain ⟨N₀, hN₀⟩ := cc.HkSq_sub_psiCut_tendsto hα hsm hmem hb hs δ hδpos
  set N : ℕ := max N₀ 1 with hNdef
  have hNge : N₀ ≤ N := le_max_left _ _
  have hN1 : 1 ≤ N := le_max_right _ _
  set χ : Fn := fun z θ => f z θ - ψ N z θ * f z θ with hχdef
  have hχSq : Work.Spaces.HkSq α 4 χ < δ := hN₀ N hNge
  have hχNrm : Work.Spaces.HkNorm α 4 χ < Real.sqrt δ := by
    rw [Work.Spaces.HkNorm]
    exact Real.sqrt_lt_sqrt (HkSq_nonneg' α 4 χ) hχSq
  -- ## 4. the cutoff product: smoothness, support, membership and `Ccφ`
  have hψf_ct : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (fun z θ => ψ N z θ * f z θ)) :=
    contDiff_psiCut_mul hs N hsm
  have hψf_supp : SuppIn (fun z θ => ψ N z θ * f z θ) (cc.zlo N) (cc.zhi N) (cc.tlo N) := by
    intro z θ h
    exact mul_eq_zero_of_left (hs.zero N z θ (by simpa only [cc.OffBox, cc.thi, cc.tlo] using h)) _
  have hψf_sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => ψ N z θ * f z θ) :=
    Work.FTS.GalLimit.Closure.smoothOpen_of_contDiff hψf_ct
  have hψf_mem : Work.Spaces.HkMem α 4 (fun z θ => ψ N z θ * f z θ) :=
    Work.FTS.GalLimit.Closure.hkMem_of_suppIn α 4 (zlo_pos N) (zlo_lt_zhi N) (tlo_pos N)
      (Work.FTS.GalLimit.Closure.smoothQuad_of_contDiff hψf_ct) hψf_supp
  have hψf_cc : Ccφ (fun z θ => ψ N z θ * f z θ) :=
    Ccφ_of_contDiff_supp (zlo_pos N) (zlo_lt_zhi N) (tlo_pos N)
      (by
        have h3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
        have hNpos : (0 : ℝ) < ((N : ℝ) + 1) := by positivity
        have hNcast : (2 : ℝ) ≤ (N : ℝ) + 1 := by
          have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
          linarith
        have h2 : 2 * cc.tlo N < Real.pi / 2 := by
          simp only [cc.tlo]
          rw [show (2 : ℝ) * (1 / ((N : ℝ) + 1)) = 2 / ((N : ℝ) + 1) by ring]
          rw [div_lt_iff₀ hNpos]
          nlinarith [h3, hNcast]
        linarith)
      hψf_ct hψf_supp
  -- ## 5. the complement function
  have hχ_sm : Work.FTS.EllipticEst.SmoothOpen χ := by
    rw [hχdef]
    exact smoothOpen_sub_all hsm hψf_sm
  have hχ_mem : Work.Spaces.HkMem α 4 χ := by
    rw [hχdef]
    exact hkMem_sub_open α 4 hsm hψf_sm hmem hψf_mem
  -- ## 6. `L₁₂` of the complement
  have hL12 : Work.Construction.L12 χ 0
      = -Work.Construction.L12 (fun z θ => ψ N z θ * f z θ) 0 := by
    have h1 := cc.L12_add_of_HkMem hψf_sm hχ_sm hψf_mem hχ_mem
    have h2 : Work.Construction.L12 (fun z θ => ψ N z θ * f z θ + χ z θ) 0
        = Work.Construction.L12 f 0 :=
      L12_congr_all (fun z θ => by rw [hχdef]; ring) 0
    rw [h2, hl] at h1
    linarith
  -- ## 7. the adjusting constant
  set c : ℝ := -Work.Construction.L12 χ 0 / c0 with hcdef
  have hcNrm : |c| ≤ C12 * Real.sqrt δ / c0 := by
    rw [hcdef, abs_div, abs_neg, abs_of_pos hc0pos]
    gcongr
    exact le_trans (hC12 α χ hχ_mem)
      (mul_le_mul_of_nonneg_left (le_of_lt hχNrm) (le_of_lt hC12pos))
  -- ## 8. the answer
  set g : Fn := fun z θ => ψ N z θ * f z θ - c * Gfar z θ with hgdef
  refine ⟨g, ?_, ?_⟩
  · -- `Coreφ`
    refine ⟨?_, ?_⟩
    · rw [hgdef]
      exact Ccφ.sub hψf_cc (Ccφ.smul c hGfar_cc)
    · -- `L₁₂ g 0 = 0`
      have hgs : ∀ z θ : ℝ, g z θ = ψ N z θ * f z θ + (-c) * Gfar z θ := by
        intro z θ
        rw [hgdef]
        ring
      have hcg_sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (-c) * Gfar z θ) :=
        Work.FTS.GalLimit.Closure.smoothOpen_of_contDiff (contDiff_const.mul hGfar_ct)
      have hcg_mem : Work.Spaces.HkMem α 4 (fun z θ => (-c) * Gfar z θ) :=
        HkMem_const_mul_all (-c) hGfar_mem
      have h1 : Work.Construction.L12 (fun z θ => ψ N z θ * f z θ + (-c) * Gfar z θ) 0
          = Work.Construction.L12 (fun z θ => ψ N z θ * f z θ) 0
            + Work.Construction.L12 (fun z θ => (-c) * Gfar z θ) 0 :=
        cc.L12_add_of_HkMem hψf_sm hcg_sm hψf_mem hcg_mem
      have h2 : Work.Construction.L12 (fun z θ => (-c) * Gfar z θ) 0
          = (-c) * Work.Construction.L12 Gfar 0 := L12_const_mul (-c) Gfar 0
      have h3 : Work.Construction.L12 (fun z θ => ψ N z θ * f z θ) 0 = c * c0 := by
        have hcc : c * c0 = -Work.Construction.L12 χ 0 := by
          rw [hcdef]
          exact div_mul_cancel₀ (-Work.Construction.L12 χ 0) hc0ne
        linarith [hL12, hcc]
      rw [L12_congr_all hgs 0, h1, h2, h3]
      have hc0' : Work.Construction.L12 Gfar 0 = c0 := rfl
      rw [hc0']
      ring
  · -- the `ℋ⁴`-bound
    have hg_sm : Work.FTS.EllipticEst.SmoothOpen g := by
      rw [hgdef]
      exact smoothOpen_sub_all hψf_sm (Work.FTS.GalLimit.Closure.smoothOpen_of_contDiff
        (contDiff_const.mul hGfar_ct))
    have hg_mem : Work.Spaces.HkMem α 4 g := by
      rw [hgdef]
      exact hkMem_sub_open α 4 hψf_sm
        (Work.FTS.GalLimit.Closure.smoothOpen_of_contDiff (contDiff_const.mul hGfar_ct)) hψf_mem
        (HkMem_const_mul_all c hGfar_mem)
    have hstep := hk_sq_api.2 α 4 f (fun z θ => ψ N z θ * f z θ) g hsm hψf_sm hg_sm hmem hψf_mem hg_mem
    -- rewrite the two error terms
    have e1 : Work.Spaces.HkSq α 4 (fun z θ => f z θ - g z θ)
        = Work.Spaces.HkSq α 4 (fun z θ => f z θ - (ψ N z θ * f z θ - c * Gfar z θ)) :=
      HkSq_congr_all (fun z θ => by rw [hgdef]) α 4
    have e2 : Work.Spaces.HkSq α 4 (fun z θ => f z θ - ψ N z θ * f z θ)
        = Work.Spaces.HkSq α 4 χ := HkSq_congr_all (fun z θ => by rw [hχdef]) α 4
    have e3 : Work.Spaces.HkSq α 4 (fun z θ => ψ N z θ * f z θ - g z θ)
        = Work.Spaces.HkSq α 4 (fun z θ => c * Gfar z θ) :=
      HkSq_congr_all (fun z θ => by rw [hgdef]; ring) α 4
    have e4 : Work.Spaces.HkSq α 4 (fun z θ => c * Gfar z θ)
        = c ^ 2 * A := by
      rw [hAdef]
      exact Work.FTS.LocData.HkSq_const_mul α 4 c hGfar_mem
    rw [e1, e2, e3, e4] at hstep
    -- the numerical bound
    have hfin : Work.Spaces.HkSq α 4 (fun z θ => f z θ - g z θ) < ε ^ 2 := by
      have hden : 0 < 1 + C12 ^ 2 * A / c0 ^ 2 := by positivity
      have hc2 : c ^ 2 ≤ (C12 * Real.sqrt δ / c0) ^ 2 := by
        rw [← sq_abs c]
        exact pow_le_pow_left₀ (abs_nonneg c) hcNrm 2
      have hA0 : 0 ≤ A := HkSq_nonneg' α 4 Gfar
      calc Work.Spaces.HkSq α 4 (fun z θ => f z θ - g z θ)
          ≤ 2 * (c ^ 2 * A) + 2 * Work.Spaces.HkSq α 4 χ := by linarith [hstep]
        _ < 2 * ((C12 * Real.sqrt δ / c0) ^ 2 * A) + 2 * δ := by
            have h1 : (c ^ 2 * A) ≤ ((C12 * Real.sqrt δ / c0) ^ 2 * A) :=
              mul_le_mul_of_nonneg_right hc2 hA0
            linarith [hχSq]
        _ = ε ^ 2 / 2 := by
            have hsq : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt (le_of_lt hδpos)
            rw [div_pow, mul_pow, hsq, hδdef]
            have hD : (1 + C12 ^ 2 * A / c0 ^ 2) ≠ 0 := ne_of_gt hden
            have hc0sq : c0 ^ 2 ≠ 0 := pow_ne_zero 2 hc0ne
            field_simp
            ring
        _ < ε ^ 2 := by nlinarith [hε]
    rw [Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => f z θ - g z θ))
        < Real.sqrt (ε ^ 2) := Real.sqrt_lt_sqrt (HkSq_nonneg' α 4 _) hfin
      _ = ε := Real.sqrt_sq (le_of_lt hε)

end Work.FTS.GalBasis
