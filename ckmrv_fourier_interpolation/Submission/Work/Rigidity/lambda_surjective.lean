/-
# Surjectivity of the modular lambda function

`λ = θ₁₀⁴/θ₀₀⁴` maps the upper half plane onto `ℂ ∖ {0,1}`.  The proof is the standard
combination of the open mapping theorem and a reduction to the standard fundamental domain:

* `λ(ℍ) = lamC '' U` is **open** (open mapping theorem for the non-constant holomorphic
  function `lamC` on the upper half plane `U = {Im > 0}`).
* `λ(ℍ)` is **relatively closed** in `ℂ ∖ {0,1}`: if `λ(τₙ) → w ≠ 0,1`, reduce `τₙ` to the
  fundamental domain `𝓕` of `SL(2,ℤ)`; the anharmonic transformation law
  (`Submission/Work/Rigidity/LambdaAnharmonic.lean`) makes `λ` of the reduced point a fixed
  anharmonic function of `λ(τₙ)`, so it converges to a point `u ∈ ℂ ∖ {0,1}`; the decay of
  `λ` at the cusp (`Work.Rigidity.lambdaFun_decay_fd`) bounds the reduced points, and a
  compactness argument produces `z ∈ ℍ` with `λ z = u`, whence `w = λ(γ z)`.
* `ℂ ∖ {0,1}` is preconnected, so an open relatively closed non-empty subset is everything.
-/
import Mathlib
import Submission.Work.Rigidity.LambdaTargets
import Submission.Work.Rigidity.LambdaAnharmonic
import Submission.Work.Rigidity.lambdaFun_decay_fd

noncomputable section

open UpperHalfPlane ModularGroup Matrix Filter Topology
open scoped MatrixGroups ModularForm
open Work.Kernels Work.Kernels.LogLambda

namespace Work.Rigidity

/-- The complement of `{0,1}` in `ℂ`, the target of `λ`. -/
def S01 : Set ℂ := {z : ℂ | z ≠ 0 ∧ z ≠ 1}

lemma mem_S01 {z : ℂ} : z ∈ S01 ↔ z ≠ 0 ∧ z ≠ 1 := Iff.rfl

/-- The bounded piece of the standard fundamental domain of `SL(2,ℤ)`, inside `ℂ`. -/
def Kfd (R : ℝ) : Set ℂ :=
  {ζ : ℂ | 1 ≤ Complex.normSq ζ ∧ |ζ.re| ≤ (1 : ℝ) / 2 ∧ 0 ≤ ζ.im ∧ ‖ζ‖ ≤ R}

lemma mem_Kfd {R : ℝ} {ζ : ℂ} :
    ζ ∈ Kfd R ↔ 1 ≤ Complex.normSq ζ ∧ |ζ.re| ≤ (1 : ℝ) / 2 ∧ 0 ≤ ζ.im ∧ ‖ζ‖ ≤ R :=
  Iff.rfl

/-! ## `λ` as `lamC` on the upper half plane -/

lemma lambdaFun_eq_lamC (τ : ℍ) : lambdaFun τ = lamC (τ : ℂ) := rfl

lemma range_lambdaFun_eq : Set.range lambdaFun = lamC '' U := by
  ext w
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨(τ : ℂ), τ.im_pos, (lambdaFun_eq_lamC τ).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, (lambdaFun_eq_lamC ⟨z, hz⟩).trans (lamC_of_mem hz).symm⟩

lemma continuous_lambdaFun : Continuous lambdaFun :=
  mdifferentiable_lambdaFun.continuous

lemma range_lambdaFun_subset_S01 : Set.range lambdaFun ⊆ S01 := by
  rintro w ⟨τ, rfl⟩
  exact ⟨lambdaFun_ne_zero τ, lambdaFun_ne_one τ⟩

/-! ## Non-constancy of `λ` -/

/-- `λ` is not constant: `λ(i) = 1/2` while `λ(i+1) = -1`. -/
lemma lambdaFun_not_constant_on_U :
    ¬ ∃ w : ℂ, ∀ z ∈ U, lamC z = w := by
  rintro ⟨w, hw⟩
  have hI : (0 : ℝ) < Complex.I.im := by simp
  have hI1 : (0 : ℝ) < (Complex.I + 1).im := by simp
  have hSτ : ModularGroup.S • (⟨Complex.I, hI⟩ : ℍ) = ⟨Complex.I, hI⟩ := by
    apply UpperHalfPlane.ext
    rw [coe_S_smul]
    simp [Complex.inv_I]
  have hhalf : lambdaFun (⟨Complex.I, hI⟩ : ℍ) = 1 / 2 := by
    have h := lambdaFun_S_eq (⟨Complex.I, hI⟩ : ℍ)
    rw [hSτ] at h
    set a := lambdaFun (⟨Complex.I, hI⟩ : ℍ) with ha
    rw [ha] at h ⊢
    linear_combination (1 / 2 : ℂ) * h
  have hTτ : lambdaFun (ModularGroup.T • (⟨Complex.I, hI⟩ : ℍ)) = -1 := by
    rw [lambdaFun_T_eq, hhalf]; norm_num
  have hIeq : ((⟨Complex.I, hI⟩ : ℍ) : ℂ) = Complex.I := rfl
  have hw1 : w = 1 / 2 := by
    have h1 : lamC Complex.I = w := hw Complex.I hI
    rw [← hIeq, ← lambdaFun_eq_lamC (⟨Complex.I, hI⟩ : ℍ), hhalf] at h1
    exact h1.symm
  have hcoec : ((ModularGroup.T • (⟨Complex.I, hI⟩ : ℍ) : ℍ) : ℂ) = Complex.I + 1 := by
    rw [coe_T_smul]
  have hw2 : w = -1 := by
    have h1 : lamC (Complex.I + 1) = w := hw (Complex.I + 1) hI1
    rw [← hcoec, ← lambdaFun_eq_lamC (ModularGroup.T • (⟨Complex.I, hI⟩ : ℍ)), hTτ] at h1
    exact h1.symm
  exact absurd hw2 (by rw [hw1]; norm_num)

/-! ## Openness of `λ(ℍ)` -/

theorem isOpen_range_lambdaFun : IsOpen (Set.range lambdaFun) := by
  have han : AnalyticOnNhd ℂ lamC U := differentiableOn_lamC.analyticOnNhd isOpen_U
  rcases han.is_constant_or_isOpen isPreconnected_U with hconst | hopen
  · exact absurd hconst lambdaFun_not_constant_on_U
  · rw [range_lambdaFun_eq]
    exact hopen U (fun _ h => h) isOpen_U

/-! ## Relative closedness of `λ(ℍ)` in `ℂ ∖ {0,1}` -/

/-- The bounded piece of the fundamental domain is compact in `ℂ`. -/
lemma isCompact_Kfd (R : ℝ) : IsCompact (Kfd R) := by
  have hA : IsClosed {ζ : ℂ | 1 ≤ Complex.normSq ζ} :=
    isClosed_le continuous_const Complex.continuous_normSq
  have hB : IsClosed {ζ : ℂ | |ζ.re| ≤ (1 : ℝ) / 2} :=
    isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const
  have hC : IsClosed {ζ : ℂ | 0 ≤ ζ.im} :=
    isClosed_le continuous_const Complex.continuous_im
  have hD : IsClosed {ζ : ℂ | ‖ζ‖ ≤ R} :=
    isClosed_le continuous_norm continuous_const
  have hclosed : IsClosed (Kfd R) := by
    rw [show Kfd R = {ζ : ℂ | 1 ≤ Complex.normSq ζ} ∩ {ζ : ℂ | |ζ.re| ≤ (1 : ℝ) / 2} ∩
        {ζ : ℂ | 0 ≤ ζ.im} ∩ {ζ : ℂ | ‖ζ‖ ≤ R} from by ext ζ; simp [Kfd, and_assoc]]
    exact ((hA.inter hB).inter hC).inter hD
  have hbdd : Bornology.IsBounded (Kfd R) :=
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset
      (fun ζ hζ => by simpa [Metric.mem_closedBall, dist_eq_norm] using hζ.2.2.2)
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbdd⟩

/-- A point of `Kfd R` has positive imaginary part. -/
lemma im_pos_of_mem_Kfd {R : ℝ} {ζ : ℂ} (hζ : ζ ∈ Kfd R) : 0 < ζ.im := by
  rcases lt_or_eq_of_le hζ.2.2.1 with h | h
  · exact h
  · exfalso
    have hre : |ζ.re| ≤ 1 / 2 := hζ.2.1
    have : Complex.normSq ζ ≤ 1 / 4 := by
      rw [Complex.normSq_apply, ← h]; nlinarith [abs_le.mp hre]
    linarith [hζ.1]

/-- **The reduction step.**  If `λ κ → w` with `w ≠ 0,1`, then some point of the fundamental
domain with `λ z` bounded away from `0,1` and bounded in norm lies in a fixed compact set. -/
theorem closure_range_lambdaFun_subset :
    closure (Set.range lambdaFun) ∩ S01 ⊆ Set.range lambdaFun := by
  rintro w ⟨hwcl, hw0, hw1⟩
  -- a sequence `τ n` with `λ (τ n) → w`
  have hε : ∀ n : ℕ, ∃ τ : ℍ, dist w (lambdaFun τ) < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨b, hb, hd⟩ := Metric.mem_closure_iff.mp hwcl (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨τ, rfl⟩ := hb
    exact ⟨τ, hd⟩
  choose τ hτ using hε
  have htend : Tendsto (fun n : ℕ => lambdaFun (τ n)) atTop (𝓝 w) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [dist_comm]; exact (hτ n).le
  -- reduce to the fundamental domain
  choose γn hγ using fun n => ModularGroup.exists_smul_mem_fd (τ n)
  let z : ℕ → ℍ := fun n => γn n • τ n
  have hzfd : ∀ n, z n ∈ ModularGroup.fd := hγ
  -- `λ (τ n)` determines `λ (z n)` by an anharmonic transformation
  have hmem : ∀ n : ℕ, ∃ i : Fin 6, anh i (lambdaFun (z n)) = lambdaFun (τ n) := by
    intro n
    have hsm : (γn n)⁻¹ • z n = τ n := by
      show (γn n)⁻¹ • (γn n • τ n) = τ n
      rw [inv_smul_smul]
    have h := lambdaFun_smul_mem_ANH (γn n)⁻¹ (z n)
    rw [hsm] at h
    exact Set.mem_range.mp h
  choose i hi using hmem
  choose j hj using fun n => anh_left_inv (i n)
  have hzlam : ∀ n, lambdaFun (z n) = anh (j n) (lambdaFun (τ n)) := by
    intro n
    rw [← hi n]
    exact (hj n (lambdaFun (z n)) (lambdaFun_ne_zero _) (lambdaFun_ne_one _)).symm
  -- a subsequence on which `j` is constant
  obtain ⟨σ, hσinf⟩ := Finite.exists_infinite_fiber j
  have hσinf' : (j ⁻¹' {σ}).Infinite := Set.infinite_coe_iff.mp hσinf
  have hSN : ∀ N : ℕ, ∃ n > N, j n = σ := by
    intro N
    by_contra h
    push_neg at h
    refine hσinf' ((Set.finite_Iic N).subset ?_)
    intro n hn
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hn
    simp only [Set.mem_Iic]
    by_contra hle
    exact h n (by omega) hn
  obtain ⟨φ, hφmono, hφσ⟩ := Nat.exists_strictMono_subsequence hSN
  have htend' : Tendsto (fun n : ℕ => lambdaFun (τ (φ n))) atTop (𝓝 w) :=
    htend.comp hφmono.tendsto_atTop
  have hzlam' : ∀ n, lambdaFun (z (φ n)) = anh σ (lambdaFun (τ (φ n))) := by
    intro n; rw [hzlam (φ n), hφσ n]
  have htendz : Tendsto (fun n : ℕ => lambdaFun (z (φ n))) atTop (𝓝 (anh σ w)) := by
    have h := (continuousAt_anh σ hw0 hw1).tendsto.comp htend'
    rw [show (fun n : ℕ => lambdaFun (z (φ n))) = fun n => anh σ (lambdaFun (τ (φ n)))
      from funext hzlam']
    exact h
  have hσ0 : anh σ w ≠ 0 := anh_ne_zero σ hw0 hw1
  have hσpos : 0 < ‖anh σ w‖ := norm_pos_iff.mpr hσ0
  -- the decay bound forces the reduced points to be bounded
  obtain ⟨R, hR⟩ := lambdaFun_decay_fd (‖anh σ w‖ / 2) (half_pos hσpos)
  have hevR : ∀ᶠ n in atTop, ‖(((z (φ n)) : ℍ) : ℂ)‖ < R := by
    have hnorm : Tendsto (fun n : ℕ => ‖lambdaFun (z (φ n)) - anh σ w‖) atTop (𝓝 0) := by
      simpa using (htendz.sub_const (anh σ w)).norm
    have hevδ : ∀ᶠ n in atTop, ‖anh σ w‖ / 2 < ‖lambdaFun (z (φ n))‖ := by
      filter_upwards [hnorm.eventually (Metric.ball_mem_nhds (0 : ℝ) (half_pos hσpos))]
        with n hn
      simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)] at hn
      have hle := (abs_le.mp (abs_norm_sub_norm_le (lambdaFun (z (φ n))) (anh σ w))).1
      linarith
    filter_upwards [hevδ] with n hn
    by_contra hcon
    have := hR (z (φ n)) (hzfd (φ n)) (not_lt.mp hcon)
    linarith
  have hevK : ∀ᶠ n in atTop, (((z (φ n)) : ℍ) : ℂ) ∈ Kfd R := by
    filter_upwards [hevR] with n hn
    have hd := hzfd (φ n)
    exact ⟨hd.1, by simpa using hd.2, by simpa using le_of_lt (z (φ n)).im_pos, hn.le⟩
  obtain ⟨a, haK, ψ, hψmono, hψtend⟩ := (isCompact_Kfd R).tendsto_subseq' hevK.frequently
  have haim : 0 < a.im := im_pos_of_mem_Kfd haK
  -- the limit `lamC a` is an anharmonic image of `w`
  have hcont : Tendsto (fun n : ℕ => lamC (((z (φ (ψ n)) : ℍ) : ℂ))) atTop (𝓝 (lamC a)) :=
    ((differentiableOn_lamC.continuousOn).continuousAt (isOpen_U.mem_nhds haim)).tendsto.comp
      hψtend
  have htendz2 : Tendsto (fun n : ℕ => lamC (((z (φ (ψ n)) : ℍ) : ℂ))) atTop (𝓝 (anh σ w)) :=
    (htendz.comp hψmono.tendsto_atTop).congr (fun n => (lambdaFun_eq_lamC (z (φ (ψ n)))))
  have hfinal : lamC a = anh σ w := tendsto_nhds_unique hcont htendz2
  obtain ⟨σ', hσ'inv⟩ := anh_left_inv σ
  obtain ⟨γ', hγ'⟩ := exists_lambdaFun_smul_eq_anh σ'
  refine ⟨γ' • (⟨a, haim⟩ : ℍ), ?_⟩
  rw [hγ' (⟨a, haim⟩ : ℍ)]
  show anh σ' (lambdaFun (⟨a, haim⟩ : ℍ)) = w
  rw [show lambdaFun (⟨a, haim⟩ : ℍ) = lamC a from rfl, hfinal]
  exact hσ'inv w hw0 hw1

/-! ## The main theorem -/

theorem lambda_surjective : Work.Rigidity.LambdaSurjective := by
  intro w hw0 hw1
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; norm_num
  have hset : S01 = ({(0 : ℂ), 1}ᶜ : Set ℂ) := by ext z; simp [S01]
  have hpre : IsPreconnected S01 := by
    have hpath : IsPathConnected (({(0 : ℂ), 1}ᶜ : Set ℂ)) :=
      Set.Countable.isPathConnected_compl_of_one_lt_rank (s := ({(0 : ℂ), 1} : Set ℂ)) hrank
        ((Set.countable_singleton (1 : ℂ)).insert 0)
    rw [hset]; exact hpath.isConnected.isPreconnected
  have hz0 : lambdaFun (⟨Complex.I, by simp⟩ : ℍ) ∈ S01 :=
    ⟨lambdaFun_ne_zero _, lambdaFun_ne_one _⟩
  have hz1 : lambdaFun (⟨Complex.I, by simp⟩ : ℍ) ∈ closure (Set.range lambdaFun) :=
    subset_closure ⟨_, rfl⟩
  have hmain : S01 ⊆ Set.range lambdaFun := by
    rcases IsPreconnected.subset_or_subset (isOpen_range_lambdaFun) (isClosed_closure.isOpen_compl)
      (by rw [Set.disjoint_compl_right_iff_subset]; exact subset_closure)
      (fun z hz => by
        by_cases h : z ∈ closure (Set.range lambdaFun)
        · exact Or.inl (closure_range_lambdaFun_subset ⟨h, hz⟩)
        · exact Or.inr h)
      hpre with h | h
    · exact h
    · exact absurd hz1 (h hz0)
  exact hmain ⟨hw0, hw1⟩

end Work.Rigidity
