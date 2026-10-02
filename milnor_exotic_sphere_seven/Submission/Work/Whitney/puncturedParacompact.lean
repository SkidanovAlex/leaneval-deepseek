import Mathlib
import Submission.Work.Thom.Basic
import Submission.Work.Thom.discSub_homotopyEquiv
import Submission.Work.Whitney.puncturedNorm
import Submission.Work.Whitney.shellParacompact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The punctured total space of a real bundle over a paracompact base is paracompact

The route: build a *continuous fibrewise norm* `fibNorm Z φ` on the total space of
`Z : VectorBundleCore ℝ B F ι` from a partition of unity `φ` subordinate to the (finite) chart
cover (`Submission/Work/Whitney/puncturedNorm.lean`), clamp the fibre vector radially into dyadic
shells `[2^k, 2^(k+1)]` (`clampPt`), and apply the gluing criterion
`paracompact_of_locallyFinite_retract_self`: the shells are paracompact
(`Work.Whitney.shellParacompact`), contained in the open annuli `{2^(k-1) < N < 2^(k+2)}` which are
locally finite, and the clamps are global retractions onto the shells.
-/

namespace Work.Whitney

universe u

open Bundle Work.TangentClasses

open scoped Topology

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type}

/-! ## The dyadic covering of the positive reals -/

/-- Every positive real lies in a dyadic shell `[2^k, 2^(k+1)]`, `k : ℤ`. -/
theorem exists_dyadic_shell {t : ℝ} (ht : 0 < t) :
    ∃ k : ℤ, (2 : ℝ) ^ k ≤ t ∧ t ≤ (2 : ℝ) ^ (k + 1) :=
  ⟨Int.log 2 t, Int.zpow_log_le_self (by norm_num) ht,
    (Int.lt_zpow_succ_log_self (b := 2) (by norm_num) t).le⟩

theorem int_bound_upper {n : ℕ} {k : ℤ} (h : k - 1 < (n : ℤ)) : k ≤ (n : ℤ) + 2 := by omega

theorem int_bound_lower {n : ℕ} {k : ℤ} (h : -(n : ℤ) < k + 2) : -(n : ℤ) - 3 ≤ k := by omega

theorem half_lt_self {x : ℝ} (hx : 0 < x) : x / 2 < x := by linarith

theorem self_lt_two_mul {x : ℝ} (hx : 0 < x) : x < 2 * x := by linarith

/-! ## The fibrewise norm on the punctured total space -/

/-- The fibrewise norm restricted to the punctured total space. -/
def pNorm [Fintype ι] (Z : VectorBundleCore ℝ B F ι) (φ : PartitionOfUnity ι B Set.univ)
    (x : ↥(Work.Thom.zeroComplement Z)) : ℝ := fibNorm Z (fun i => φ i) x.1

theorem continuous_pNorm [Fintype ι] (Z : VectorBundleCore ℝ B F ι)
    (φ : PartitionOfUnity ι B Set.univ) (hφ : φ.IsSubordinate Z.baseSet) :
    Continuous (pNorm Z φ) :=
  (continuous_fibNorm Z (fun i => φ i) hφ).comp continuous_subtype_val

theorem pNorm_pos [Fintype ι] (Z : VectorBundleCore ℝ B F ι)
    (φ : PartitionOfUnity ι B Set.univ) (hφ : φ.IsSubordinate Z.baseSet)
    (x : ↥(Work.Thom.zeroComplement Z)) : 0 < pNorm Z φ x :=
  fibNorm_pos Z hφ x.1 x.2

/-- Positive homogeneity of the punctured norm. -/
theorem pNorm_smul [Fintype ι] (Z : VectorBundleCore ℝ B F ι) (φ : PartitionOfUnity ι B Set.univ)
    (x : ↥(Work.Thom.zeroComplement Z)) {c : ℝ} (hc : 0 ≤ c)
    (h : (show F from c • x.1.2) ≠ 0) :
    pNorm Z φ ⟨⟨x.1.1, c • x.1.2⟩, (Work.Thom.mem_zeroComplement _).mpr h⟩ = c * pNorm Z φ x :=
  fibNorm_smul Z (fun i => φ i) x.1.1 hc x.1.2

/-! ## The dyadic clamping -/

/-- The coefficient by which the fibre vector of a point of norm `t` must be scaled so that its
fibrewise norm becomes `max 2^k (min t 2^(k+1))`, i.e. its norm clamped into `[2^k, 2^(k+1)]`. -/
def clampCoeff (k : ℤ) (t : ℝ) : ℝ := max ((2 : ℝ) ^ k) (min t ((2 : ℝ) ^ (k + 1))) / t

theorem clampCoeff_mul (k : ℤ) {t : ℝ} (ht : 0 < t) :
    clampCoeff k t * t = max ((2 : ℝ) ^ k) (min t ((2 : ℝ) ^ (k + 1))) :=
  div_mul_cancel₀ _ (ne_of_gt ht)

theorem clampCoeff_pos (k : ℤ) {t : ℝ} (ht : 0 < t) : 0 < clampCoeff k t :=
  div_pos (lt_of_lt_of_le (zpow_pos (by norm_num : (0 : ℝ) < 2) k) (le_max_left _ _)) ht

theorem clampCoeff_mem (k : ℤ) {t : ℝ} (ht : 0 < t) :
    (2 : ℝ) ^ k ≤ clampCoeff k t * t ∧ clampCoeff k t * t ≤ (2 : ℝ) ^ (k + 1) := by
  refine ⟨?_, ?_⟩
  · rw [clampCoeff_mul k ht]; exact le_max_left _ _
  · rw [clampCoeff_mul k ht]
    refine max_le ?_ (min_le_right _ _)
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)

theorem clampCoeff_eq_one (k : ℤ) {t : ℝ} (ht : 0 < t)
    (h : (2 : ℝ) ^ k ≤ t ∧ t ≤ (2 : ℝ) ^ (k + 1)) : clampCoeff k t = 1 := by
  have hmax : max ((2 : ℝ) ^ k) (min t ((2 : ℝ) ^ (k + 1))) = t := by
    rw [min_eq_left h.2, max_eq_right h.1]
  rw [clampCoeff, hmax, div_self (ne_of_gt ht)]

/-- A positive scalar times a nonzero vector is nonzero. -/
theorem smul_ne_zero_of_pos {c : ℝ} (hc : 0 < c) {v : F} (hv : v ≠ 0) : c • v ≠ 0 := by
  intro h
  have h0 : ‖c • v‖ = 0 := by rw [h, norm_zero]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc] at h0
  exact mul_ne_zero (ne_of_gt hc) (norm_ne_zero_iff.mpr hv) h0

/-- The **dyadic clamping map** on the punctured total space: the fibre vector is rescaled so that
its fibrewise norm is clamped into `[2^k, 2^(k+1)]`. -/
def clampPt [Fintype ι] (Z : VectorBundleCore ℝ B F ι) (φ : PartitionOfUnity ι B Set.univ)
    (hφ : φ.IsSubordinate Z.baseSet) (k : ℤ) (x : ↥(Work.Thom.zeroComplement Z)) :
    ↥(Work.Thom.zeroComplement Z) :=
  ⟨⟨x.1.1, clampCoeff k (pNorm Z φ x) • x.1.2⟩,
    (Work.Thom.mem_zeroComplement _).mpr
      (smul_ne_zero_of_pos (clampCoeff_pos k (pNorm_pos Z φ hφ x))
        ((Work.Thom.mem_zeroComplement x.1).mp x.2))⟩

theorem pNorm_clampPt [Fintype ι] (Z : VectorBundleCore ℝ B F ι)
    (φ : PartitionOfUnity ι B Set.univ) (hφ : φ.IsSubordinate Z.baseSet) (k : ℤ)
    (x : ↥(Work.Thom.zeroComplement Z)) :
    pNorm Z φ (clampPt Z φ hφ k x) =
      max ((2 : ℝ) ^ k) (min (pNorm Z φ x) ((2 : ℝ) ^ (k + 1))) := by
  have hx : 0 < pNorm Z φ x := pNorm_pos Z φ hφ x
  have hne : (show F from clampCoeff k (pNorm Z φ x) • x.1.2) ≠ 0 :=
    smul_ne_zero_of_pos (clampCoeff_pos k hx) ((Work.Thom.mem_zeroComplement x.1).mp x.2)
  show pNorm Z φ ⟨⟨x.1.1, clampCoeff k (pNorm Z φ x) • x.1.2⟩, _⟩ = _
  rw [pNorm_smul Z φ x (le_of_lt (clampCoeff_pos k hx)) hne, clampCoeff_mul k hx]

theorem clampPt_mem [Fintype ι] (Z : VectorBundleCore ℝ B F ι)
    (φ : PartitionOfUnity ι B Set.univ) (hφ : φ.IsSubordinate Z.baseSet) (k : ℤ)
    (x : ↥(Work.Thom.zeroComplement Z)) :
    (2 : ℝ) ^ k ≤ pNorm Z φ (clampPt Z φ hφ k x) ∧
      pNorm Z φ (clampPt Z φ hφ k x) ≤ (2 : ℝ) ^ (k + 1) := by
  rw [pNorm_clampPt]
  refine ⟨le_max_left _ _, max_le ?_ (min_le_right _ _)⟩
  exact zpow_le_zpow_right₀ (by norm_num) (by omega)

theorem clampPt_fixes [Fintype ι] (Z : VectorBundleCore ℝ B F ι)
    (φ : PartitionOfUnity ι B Set.univ) (hφ : φ.IsSubordinate Z.baseSet) (k : ℤ)
    (x : ↥(Work.Thom.zeroComplement Z))
    (hx : (2 : ℝ) ^ k ≤ pNorm Z φ x ∧ pNorm Z φ x ≤ (2 : ℝ) ^ (k + 1)) :
    clampPt Z φ hφ k x = x := by
  have hc : clampCoeff k (pNorm Z φ x) = 1 := clampCoeff_eq_one k (pNorm_pos Z φ hφ x) hx
  have htot : (⟨x.1.1, clampCoeff k (pNorm Z φ x) • x.1.2⟩ : Z.TotalSpace) = x.1 := by
    rw [hc, one_smul]
  apply Subtype.ext
  exact htot

theorem continuous_clampPt [Fintype ι] (Z : VectorBundleCore ℝ B F ι)
    (φ : PartitionOfUnity ι B Set.univ) (hφ : φ.IsSubordinate Z.baseSet) (k : ℤ) :
    Continuous (clampPt Z φ hφ k) := by
  have hc : Continuous fun x : ↥(Work.Thom.zeroComplement Z) => clampCoeff k (pNorm Z φ x) := by
    unfold clampCoeff
    exact (continuous_const.max ((continuous_pNorm Z φ hφ).min continuous_const)).div
      (continuous_pNorm Z φ hφ) (fun x => ne_of_gt (pNorm_pos Z φ hφ x))
  have hcont : Continuous fun x : ↥(Work.Thom.zeroComplement Z) =>
      (⟨x.1.1, clampCoeff k (pNorm Z φ x) • x.1.2⟩ : Z.TotalSpace) :=
    Work.Thom.continuous_smul_section_univ Z ⟨Subtype.val, continuous_subtype_val⟩
      ⟨fun x => clampCoeff k (pNorm Z φ x), hc⟩
  exact hcont.subtype_mk _

/-! ## The gluing criterion for paracompactness -/

/-- **Gluing criterion for paracompactness.**  If `X` is the union of a `ℤ`-indexed family of
subspaces `F n`, each paracompact, each contained in an open `O n`, with `{O n}` locally finite, and
each `F n` is a retract of `X` (`ρ n : X → X` continuous with `ρ n x ∈ F n` always and `ρ n x = x`
for `x ∈ F n`), then `X` is paracompact.  No closedness of `F n` and no separation hypothesis is
needed. -/
theorem paracompact_of_locallyFinite_retract_self {X : Type u} [TopologicalSpace X]
    (O F : ℤ → Set X) (hOopen : ∀ n, IsOpen (O n)) (hOfin : LocallyFinite O)
    (hFO : ∀ n, F n ⊆ O n) (hcov : ⋃ n, F n = Set.univ)
    (hpar : ∀ n, ParacompactSpace ↥(F n))
    (ρ : ℤ → X → X) (hρcont : ∀ n, Continuous (ρ n))
    (hρmem : ∀ n (x : X), ρ n x ∈ F n)
    (hρfix : ∀ n (x : X) (hx : x ∈ F n), ρ n x = x) :
    ParacompactSpace X := by
  classical
  let ρ' (n : ℤ) : C(X, ↥(F n)) := ⟨fun x => ⟨ρ n x, hρmem n x⟩, (hρcont n).subtype_mk _⟩
  have hρ'fix : ∀ n (x : X) (hx : x ∈ F n), ρ' n x = (⟨x, hx⟩ : ↥(F n)) := by
    intro n x hx
    exact Subtype.ext (hρfix n x hx)
  refine ⟨fun α s hs hsuniv => ?_⟩
  have hV : ∀ n, ∃ V : α → Set ↥(F n), (∀ a, IsOpen (V a)) ∧ (⋃ a, V a = Set.univ) ∧
      LocallyFinite V ∧ ∀ a, V a ⊆ {y | y.1 ∈ s a} := by
    intro n
    refine precise_refinement (fun a : α => {y : ↥(F n) | y.1 ∈ s a}) (fun a => ?_) ?_
    · exact (hs a).preimage continuous_subtype_val
    · rw [Set.eq_univ_iff_forall]
      intro y
      have hy : y.1 ∈ ⋃ a, s a := by rw [hsuniv]; exact Set.mem_univ _
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr ⟨a, ha⟩
  choose V hVopen hVcov hVfin hVsub using hV
  refine ⟨ℤ × α, fun p => ((ρ' p.1) ⁻¹' (V p.1 p.2)) ∩ (O p.1) ∩ (s p.2), ?_, ?_, ?_, ?_⟩
  · rintro ⟨n, a⟩
    exact (((hVopen n a).preimage (ρ' n).continuous).inter (hOopen n)).inter (hs a)
  · rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (show x ∈ ⋃ n, F n by rw [hcov]; exact Set.mem_univ x)
    have hxV : (⟨x, hn⟩ : ↥(F n)) ∈ ⋃ a, V n a := by rw [hVcov n]; exact Set.mem_univ _
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hxV
    refine Set.mem_iUnion.mpr ⟨(n, a), ⟨?_, hFO n hn⟩, (hVsub n a) ha⟩
    rw [Set.mem_preimage, hρ'fix n x hn]
    exact ha
  · -- local finiteness
    intro x
    obtain ⟨t, ht, hSfin⟩ := hOfin x
    obtain ⟨t', ⟨hxt', ht'open⟩, ht't⟩ := (nhds_basis_opens x).mem_iff.mp ht
    have hU : ∀ n, ∃ u : Set X, IsOpen u ∧ x ∈ u ∧
        {a | ((ρ' n) ⁻¹' (V n a) ∩ u).Nonempty}.Finite := by
      intro n
      obtain ⟨w, hwmem, hwfin⟩ := hVfin n (ρ' n x)
      obtain ⟨u, ⟨hxu, huopen⟩, huw⟩ := (nhds_basis_opens (ρ' n x)).mem_iff.mp hwmem
      refine ⟨(ρ' n) ⁻¹' u, huopen.preimage (ρ' n).continuous, hxu, hwfin.subset ?_⟩
      rintro a ⟨y, hy1, hy2⟩
      exact ⟨(ρ' n) y, hy1, huw hy2⟩
    choose U hUopen hxU hUfin using hU
    refine ⟨t' ∩ ⋂ n ∈ hSfin.toFinset, U n, ?_, ?_⟩
    · refine (ht'open.inter (isOpen_biInter_finset fun n _ => hUopen n)).mem_nhds ⟨hxt', ?_⟩
      exact Set.mem_biInter fun n _ => hxU n
    · refine Set.Finite.subset (hSfin.biUnion fun n _ => (hUfin n).image (fun a => (n, a))) ?_
      rintro ⟨n, a⟩ ⟨y, hy1, hy2⟩
      have hyn : y ∈ O n := hy1.1.2
      have hyt : y ∈ t := ht't hy2.1
      have hSn : n ∈ {i | (O i ∩ t).Nonempty} := ⟨y, hyn, hyt⟩
      have hSn' : n ∈ hSfin.toFinset := by rw [hSfin.mem_toFinset]; exact hSn
      have hyU : y ∈ U n := (Set.mem_iInter₂.mp hy2.2) n hSn'
      refine Set.mem_biUnion hSn ?_
      exact (Set.mem_image (fun a => (n, a))
        {a | ((ρ' n) ⁻¹' (V n a) ∩ U n).Nonempty} (n, a)).mpr
        ⟨a, ⟨y, hy1.1.1, hyU⟩, rfl⟩
  · rintro ⟨n, a⟩
    exact ⟨a, fun z hz => hz.2⟩

/-! ## Assembly -/

variable [ParacompactSpace B] [T2Space B] [FiniteDimensional ℝ F] [Fintype ι]

theorem puncturedParacompact_aux (Z : VectorBundleCore ℝ B F ι)
    (φ : PartitionOfUnity ι B Set.univ) (hφ : φ.IsSubordinate Z.baseSet) :
    ParacompactSpace ↥(Work.Thom.zeroComplement Z) := by
  classical
  have hN : Continuous (pNorm Z φ) := continuous_pNorm Z φ hφ
  have hNpos : ∀ x : ↥(Work.Thom.zeroComplement Z), 0 < pNorm Z φ x := pNorm_pos Z φ hφ
  let Fk : ℤ → Set ↥(Work.Thom.zeroComplement Z) := fun k =>
    {x | (2 : ℝ) ^ k ≤ pNorm Z φ x ∧ pNorm Z φ x ≤ (2 : ℝ) ^ (k + 1)}
  let Ok : ℤ → Set ↥(Work.Thom.zeroComplement Z) := fun k =>
    {x | (2 : ℝ) ^ (k - 1) < pNorm Z φ x ∧ pNorm Z φ x < (2 : ℝ) ^ (k + 2)}
  have hOopen : ∀ k, IsOpen (Ok k) := fun k =>
    (isOpen_lt continuous_const hN).inter (isOpen_lt hN continuous_const)
  have hFO : ∀ k, Fk k ⊆ Ok k := by
    intro k x hx
    refine ⟨lt_of_lt_of_le ?_ hx.1, lt_of_le_of_lt hx.2 ?_⟩
    · exact zpow_lt_zpow_right₀ (by norm_num) (by omega)
    · exact zpow_lt_zpow_right₀ (by norm_num) (by omega)
  have hcov : ⋃ k, Fk k = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨k, hk⟩ := exists_dyadic_shell (hNpos x)
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  have hpar : ∀ k, ParacompactSpace ↥(Fk k) := fun k => shellParacompact Z hφ k
  have hρmem : ∀ k (x : ↥(Work.Thom.zeroComplement Z)), clampPt Z φ hφ k x ∈ Fk k :=
    fun k x => clampPt_mem Z φ hφ k x
  have hρfix : ∀ k (x : ↥(Work.Thom.zeroComplement Z)) (hx : x ∈ Fk k),
      clampPt Z φ hφ k x = x := fun k x hx => clampPt_fixes Z φ hφ k x hx
  have hOfin : LocallyFinite Ok := by
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt (max (2 * pNorm Z φ x) (2 / pNorm Z φ x))
    have h2n : max (2 * pNorm Z φ x) (2 / pNorm Z φ x) < (2 : ℝ) ^ n :=
      lt_of_lt_of_le hn (by exact_mod_cast Nat.lt_two_pow_self.le)
    have hIoo : {y : ↥(Work.Thom.zeroComplement Z) |
        pNorm Z φ y ∈ Set.Ioo (pNorm Z φ x / 2) (2 * pNorm Z φ x)} ∈ 𝓝 x := by
      refine ((isOpen_lt continuous_const hN).inter (isOpen_lt hN continuous_const)).mem_nhds ?_
      exact ⟨half_lt_self (hNpos x), self_lt_two_mul (hNpos x)⟩
    refine ⟨{y | pNorm Z φ y ∈ Set.Ioo (pNorm Z φ x / 2) (2 * pNorm Z φ x)}, hIoo, ?_⟩
    refine Set.Finite.subset (Set.finite_Icc (-(n : ℤ) - 3) ((n : ℤ) + 2)) ?_
    rintro k ⟨y, hyk, hyIoo⟩
    have ht2 : 2 * pNorm Z φ x < (2 : ℝ) ^ n := lt_of_le_of_lt (le_max_left _ _) h2n
    have ht1 : 2 < (2 : ℝ) ^ n * pNorm Z φ x := by
      have h := lt_of_le_of_lt (le_max_right _ _) h2n
      rw [div_lt_iff₀ (hNpos x)] at h
      exact h
    have hub : k - 1 < (n : ℤ) := by
      rw [← zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)]
      exact lt_trans hyk.1 (lt_trans hyIoo.2 ht2)
    have hpow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
    have h1 : (2 : ℝ) ^ (-(n : ℤ)) < pNorm Z φ x / 2 := by
      rw [zpow_neg, zpow_natCast]
      rw [inv_lt_iff_one_lt_mul₀ hpow]
      nlinarith [ht1, hNpos x]
    have hlb : -(n : ℤ) < k + 2 := by
      rw [← zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)]
      exact lt_trans h1 (lt_trans hyIoo.1 hyk.2)
    exact ⟨int_bound_lower hlb, int_bound_upper hub⟩
  exact paracompact_of_locallyFinite_retract_self Ok Fk hOopen hOfin hFO hcov hpar
    (fun k => clampPt Z φ hφ k) (fun k => continuous_clampPt Z φ hφ k) hρmem hρfix

end

/-- **The punctured total space of a finite-rank real bundle over a paracompact Hausdorff base is
paracompact.**  This is the instance the Whitney induction needs: peeling a summand of `E ⊕ F` is
injective on cohomology over the punctured total space (`Work.Thom.bijective_proj_zeroComplementA`),
but the induction hypothesis is applied to bundles *over that punctured space*, so it must be
paracompact.

PROOF PLAN (bundle over a paracompact base with a `σ`-compact, locally compact fibre is
paracompact; only the finite-dimensional model-fibre case is stated).

Let `Y = ↥(zeroComplement Z)`.  Choose a locally finite family `{U_λ}` of open sets covering `B`,
each contained in some `Z.baseSet i`, and shrink it to a locally finite `{W_λ}` with
`closure W_λ ⊆ U_λ` (paracompact `T2` ⟹ normal, `precise_refinement_set`).  Fix a compact exhaustion
`K_0 ⊆ K_1 ⊆ ...` of `F`, `⋃ K_n = F`, `K_n ⊆ interior K_{n+1}` (finite-dimensional `F` is proper,
`K_n = closedBall 0 n` works).

* For `λ`, `n`, the set `P_{λ,n} := {p : Y | π p ∈ closure W_λ ∧ (Z.localTriv i_λ p).2 ∈ K_n}` is
  closed in `Y` (the trivialization is a homeomorphism on the closed set `π ⁻¹' closure W_λ`), and
  `P_{λ,n} → closure W_λ` is a continuous surjection with compact fibres `K_n` satisfying the tube
  property (over the chart it is the projection of the product `closure W_λ × K_n`); hence `P_{λ,n}`
  is paracompact by `Work.LerayHirsch.paracompactSpace_of_compact_fibres`.
* `Y = ⋃_n Y_n` with `Y_n := ⋃_λ (P_{λ,n+1} ∖ P_{λ,n-1})` (the slab over the annulus
  `K_{n+1} ∖ interior K_{n-1}`): each `Y_n` is closed in `Y` and a locally finite union of closed
  paracompact subspaces, hence paracompact (locally finite unions of closed paracompact subspaces are
  paracompact — the `precise_refinement_set` argument); every point of `Y` lies in the interior of at
  most two `Y_n`.
* Finish with the "increasing closed cover with locally finite interiors" argument (the same one as
  for `X × ℝ`, `X` paracompact): build a locally finite open refinement on each `Y_n` and glue; local
  finiteness follows since closures stay inside `Y_n` and each point meets finitely many `Y_n`.

Two reviewers approved: the statement is true, non-vacuous, and exactly the missing instance for
`Work.Whitney.wfBelow_peelStep` (`failed to synthesize ParacompactSpace
↑(Thom.zeroComplement (Thom.realification A))`).  `T2Space ↥(zeroComplement Z)` is available
separately (`Work.Tubular.PuncturedDiscPair.t2Space_totalSpace`), so it is not part of the
statement, but it will be needed inside the proof.  Add helper lemmas above the statement freely. -/
theorem puncturedParacompact {B : Type} [TopologicalSpace B] [ParacompactSpace B]
    [T2Space B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {ι : Type} [Fintype ι] (Z : Work.TangentClasses.RealBundle B F ι) :
    ParacompactSpace ↥(Work.Thom.zeroComplement Z) := by
  obtain ⟨φ, hφ⟩ := exists_partitionOfUnity_subordinate Z
  exact puncturedParacompact_aux Z φ hφ

end Work.Whitney
