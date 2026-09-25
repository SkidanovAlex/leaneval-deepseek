/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The flat Seeley extension operator: definitions

Given weights `a : ℕ → ℝ` and scales `b : ℕ → ℝ` with `b m ≥ 2`, `b m → ∞` and the moment
identities `∑' m, a m * (-(b m))^j = 1`, we define the flat Seeley extension operator for
functions on the half space `{p : X × ℝ | 0 < p.2}`, extended to the slab `{p | -δ < p.2}`.

The operator is

  `seeleyEV a b δ g p = g p`  for `0 ≤ p.2`, and
  `seeleyEV a b δ g p = ∑' m, a m • (χ (-(b m) * p.2) • (ρ • g) (p.1, -(b m) * p.2))`  for `p.2 < 0`,

where `χ` is a smooth cutoff equal to `1` near `0` and supported in `[-2,2]`, and `ρ` is a smooth
cutoff equal to `1` on `[-δ/2, ∞)` and vanishing on `(-∞, -3δ/4]` (so that `ρ • g` is smooth on all
of `X × ℝ` whenever `g` is smooth on the slab `{-δ < p.2}`).

All the scalar multiplications are the real scalar multiplications of `ℂ` (writing `c • z` for a
real `c` and a complex `z`), which keeps the type class instances unambiguous.
-/
import Mathlib
import Submission.Work.NN.Final.SeeleyDefs

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

set_option linter.unusedSectionVars false

namespace Work.NN.Final

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- From `C^n` for every natural `n` follows `C^∞`. -/
lemma contDiff_infty_of_forall_nat {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {f : Y → Z}
    (h : ∀ m : ℕ, ContDiff ℝ (m : WithTop ENat) f) : ContDiff ℝ ∞ f :=
  contDiff_iff_forall_nat_le (n := ⊤) |>.mpr (fun m _ => h m)

/-! ## The normal cutoff `ρ` -/

/-- The cutoff localising the extension to a neighbourhood of the closed half space:
it equals `1` on `[-δ/2, ∞)` and `0` on `(-∞, -3δ/4]`. -/
def seeleyRho (δ : ℝ) : ℝ → ℝ := fun s => Real.smoothTransition ((4 * s + 3 * δ) / δ)

lemma seeleyRho_contDiff (δ : ℝ) : ContDiff ℝ ∞ (seeleyRho δ) := by
  have h1 : ContDiff ℝ ∞ (fun s : ℝ => (4 * s + 3 * δ) / δ) := by fun_prop
  exact Real.smoothTransition.contDiff.comp h1

lemma seeleyRho_contDiff_fin (δ : ℝ) (m : ℕ) :
    ContDiff ℝ (m : WithTop ENat) (seeleyRho δ) := by
  have h1 : ContDiff ℝ (m : WithTop ENat) (fun s : ℝ => (4 * s + 3 * δ) / δ) := by fun_prop
  exact (Real.smoothTransition.contDiff.of_le (WithTop.coe_le_coe.mpr le_top)).comp h1

lemma seeleyRho_eq_one {δ s : ℝ} (hδ : 0 < δ) (hs : -(δ / 2) ≤ s) : seeleyRho δ s = 1 := by
  unfold seeleyRho
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ hδ]
  linarith

lemma seeleyRho_eq_zero {δ s : ℝ} (hδ : 0 < δ) (hs : s ≤ -(3 * δ / 4)) : seeleyRho δ s = 0 := by
  unfold seeleyRho
  apply Real.smoothTransition.zero_of_nonpos
  rw [div_le_iff₀ hδ]
  linarith

lemma seeleyRho_nonneg (δ s : ℝ) : 0 ≤ seeleyRho δ s := by
  unfold seeleyRho
  exact Real.smoothTransition.nonneg _

lemma seeleyRho_le_one (δ s : ℝ) : seeleyRho δ s ≤ 1 := by
  unfold seeleyRho
  exact Real.smoothTransition.le_one _

/-! ## The localised function `ρ • g` -/

/-- `g` multiplied by the normal cutoff: smooth on all of `X × ℝ` when `g` is smooth on the
slab `{-δ < p.2}`. -/
def seeleyV (δ : ℝ) (g : X × ℝ → ℂ) : X × ℝ → ℂ := fun p => (seeleyRho δ p.2) • g p

lemma seeleyV_eq (δ : ℝ) (g : X × ℝ → ℂ) {hδ : 0 < δ} {p : X × ℝ} (hp : -(δ / 2) ≤ p.2) :
    seeleyV δ g p = g p := by
  simp only [seeleyV, seeleyRho_eq_one hδ hp, one_smul]

lemma seeleyV_zero (δ : ℝ) (g : X × ℝ → ℂ) (hδ : 0 < δ) {p : X × ℝ}
    (hp : p.2 ≤ -(3 * δ / 4)) : seeleyV δ g p = 0 := by
  simp only [seeleyV, seeleyRho_eq_zero hδ hp, zero_smul]

/-- `seeleyV` is `C^n` on all of `X × ℝ` when `g` is smooth on the slab `{-δ < p.2}`. -/
lemma seeleyV_contDiff_fin {δ : ℝ} (hδ : 0 < δ) {g : X × ℝ → ℂ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) g {p : X × ℝ | -δ < p.2}) (M : ℕ) :
    ContDiff ℝ (M : WithTop ENat) (seeleyV δ g) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.2 < -(3 * δ / 4)
  · have hneigh : {q : X × ℝ | q.2 < -(3 * δ / 4)} ∈ 𝓝 p :=
      (isOpen_lt continuous_snd continuous_const).mem_nhds hp
    have hev : seeleyV δ g =ᶠ[𝓝 p] (fun _ => 0) := by
      filter_upwards [hneigh] with q hq
      exact seeleyV_zero δ g hδ (le_of_lt hq)
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · push_neg at hp
    have hpδ : -δ < p.2 := by linarith
    have hmem : {q : X × ℝ | -δ < q.2} ∈ 𝓝 p :=
      (isOpen_lt continuous_const continuous_snd).mem_nhds hpδ
    have hg' : ContDiffAt ℝ (M : WithTop ENat) g p := (hg M).contDiffAt hmem
    have hρ : ContDiffAt ℝ (M : WithTop ENat) (fun q : X × ℝ => seeleyRho δ q.2) p :=
      ((seeleyRho_contDiff_fin δ M).comp (contDiff_snd (E := X))).contDiffAt
    have h := hρ.smul hg'
    change ContDiffAt ℝ (M : WithTop ENat) (fun x : X × ℝ => (seeleyRho δ x.2) • g x) p
    exact h

/-- `seeleyV` is `C^∞` on all of `X × ℝ` when `g` is smooth on the slab `{-δ < p.2}`. -/
lemma seeleyV_contDiff {δ : ℝ} (hδ : 0 < δ) {g : X × ℝ → ℂ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) g {p : X × ℝ | -δ < p.2}) :
    ContDiff ℝ ∞ (seeleyV δ g) :=
  contDiff_infty_of_forall_nat (fun m => seeleyV_contDiff_fin hδ hg m)

/-! ## The Seeley terms and the extension operator -/

/-- The `m`-th term of the Seeley sum (with the localised function `seeleyV`). -/
def seeleyTV (a b : ℕ → ℝ) (δ : ℝ) (g : X × ℝ → ℂ) (m : ℕ) (p : X × ℝ) : ℂ :=
  (a m) • ((seeleyCut (-(b m) * p.2)) • seeleyV δ g (p.1, -(b m) * p.2))

/-- The Seeley sum, a function on all of `X × ℝ`. -/
def seeleySumV (a b : ℕ → ℝ) (δ : ℝ) (g : X × ℝ → ℂ) (p : X × ℝ) : ℂ :=
  ∑' m, seeleyTV a b δ g m p

/-- The Seeley extension operator. -/
def seeleyEV (a b : ℕ → ℝ) (δ : ℝ) (g : X × ℝ → ℂ) (p : X × ℝ) : ℂ :=
  if 0 ≤ p.2 then g p else seeleySumV a b δ g p

lemma seeleyEV_of_nonneg (a b : ℕ → ℝ) (δ : ℝ) (g : X × ℝ → ℂ) {p : X × ℝ} (hp : 0 ≤ p.2) :
    seeleyEV a b δ g p = g p := ite_eq_left hp

lemma seeleyEV_of_neg (a b : ℕ → ℝ) (δ : ℝ) (g : X × ℝ → ℂ) {p : X × ℝ} (hp : p.2 < 0) :
    seeleyEV a b δ g p = seeleySumV a b δ g p := ite_eq_right (not_le.mpr hp)

lemma seeleyTV_add (a b : ℕ → ℝ) (δ : ℝ) (g₁ g₂ : X × ℝ → ℂ) (m : ℕ) (p : X × ℝ) :
    seeleyTV a b δ (g₁ + g₂) m p = seeleyTV a b δ g₁ m p + seeleyTV a b δ g₂ m p := by
  simp only [seeleyTV, seeleyV, Pi.add_apply, smul_add]

lemma seeleyTV_smul (a b : ℕ → ℝ) (δ : ℝ) (c : ℝ) (g : X × ℝ → ℂ) (m : ℕ) (p : X × ℝ) :
    seeleyTV a b δ (c • g) m p = c • seeleyTV a b δ g m p := by
  simp only [seeleyTV, seeleyV, Pi.smul_apply, smul_smul]
  congr 1
  ring

/-- For `p` with `p.2 < 0`, only finitely many terms of the Seeley sum are non-zero. -/
lemma exists_finset_seeleyTV_eq_zero {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop)
    (δ : ℝ) (g : X × ℝ → ℂ) {p : X × ℝ} (hp : p.2 < 0) :
    ∃ S : Finset ℕ, ∀ m ∉ S, seeleyTV a b δ g m p = 0 := by
  obtain ⟨M, hM⟩ := exists_b_ge hbT (2 / |p.2|)
  refine ⟨Finset.range M, fun m hm => ?_⟩
  simp only [Finset.mem_range, not_lt] at hm
  have hpabs : 0 < |p.2| := abs_pos.mpr (ne_of_lt hp)
  have hle : 2 / |p.2| ≤ b m := hM m hm
  have hge : 2 ≤ b m * |p.2| := by
    rw [div_le_iff₀ hpabs] at hle; linarith
  have harg : 2 ≤ |-(b m) * p.2| := by
    rw [abs_neg_mul, abs_of_nonneg (by linarith [hb m] : (0:ℝ) ≤ b m)]
    exact hge
  simp only [seeleyTV, seeleyCut_eq_zero harg, zero_smul, smul_zero]


/-- The Seeley sum is additive in the function, on the negative half space. -/
lemma seeleySumV_add {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (δ : ℝ) (g₁ g₂ : X × ℝ → ℂ)
    {p : X × ℝ} (hp : p.2 < 0) :
    seeleySumV a b δ (g₁ + g₂) p = seeleySumV a b δ g₁ p + seeleySumV a b δ g₂ p := by
  obtain ⟨S₁, hS₁⟩ := exists_finset_seeleyTV_eq_zero hb hbT δ g₁ hp
  obtain ⟨S₂, hS₂⟩ := exists_finset_seeleyTV_eq_zero hb hbT δ g₂ hp
  obtain ⟨S₃, hS₃⟩ := exists_finset_seeleyTV_eq_zero hb hbT δ (g₁ + g₂) hp
  rw [seeleySumV, seeleySumV, seeleySumV, tsum_eq_sum (s := S₃) hS₃,
    tsum_eq_sum (s := S₁) hS₁, tsum_eq_sum (s := S₂) hS₂]
  have e1 : (∑ m ∈ S₃, seeleyTV a b δ (g₁ + g₂) m p)
      = ∑ m ∈ S₃ ∪ S₁ ∪ S₂, seeleyTV a b δ (g₁ + g₂) m p :=
    Finset.sum_subset (fun m hm => by simp only [Finset.mem_union]; tauto)
      (fun m _ hm => hS₃ m hm)
  have e2 : (∑ m ∈ S₁, seeleyTV a b δ g₁ m p) = ∑ m ∈ S₃ ∪ S₁ ∪ S₂, seeleyTV a b δ g₁ m p :=
    Finset.sum_subset (fun m hm => by simp only [Finset.mem_union]; tauto)
      (fun m _ hm => hS₁ m hm)
  have e3 : (∑ m ∈ S₂, seeleyTV a b δ g₂ m p) = ∑ m ∈ S₃ ∪ S₁ ∪ S₂, seeleyTV a b δ g₂ m p :=
    Finset.sum_subset (fun m hm => by simp only [Finset.mem_union]; tauto)
      (fun m _ hm => hS₂ m hm)
  rw [e1, e2, e3, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => seeleyTV_add a b δ g₁ g₂ m p

/-- The Seeley sum is homogeneous in the function, on the negative half space. -/
lemma seeleySumV_smul {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (δ : ℝ) (c : ℝ) (g : X × ℝ → ℂ)
    {p : X × ℝ} (hp : p.2 < 0) :
    seeleySumV a b δ (c • g) p = c • seeleySumV a b δ g p := by
  obtain ⟨S₁, hS₁⟩ := exists_finset_seeleyTV_eq_zero hb hbT δ g hp
  obtain ⟨S₂, hS₂⟩ := exists_finset_seeleyTV_eq_zero hb hbT δ (c • g) hp
  rw [seeleySumV, seeleySumV, tsum_eq_sum (s := S₁) hS₁, tsum_eq_sum (s := S₂) hS₂]
  have e1 : (∑ m ∈ S₂, seeleyTV a b δ (c • g) m p)
      = ∑ m ∈ S₂ ∪ S₁, seeleyTV a b δ (c • g) m p :=
    Finset.sum_subset (fun m hm => by simp only [Finset.mem_union]; tauto)
      (fun m _ hm => hS₂ m hm)
  have e2 : (∑ m ∈ S₁, seeleyTV a b δ g m p) = ∑ m ∈ S₂ ∪ S₁, seeleyTV a b δ g m p :=
    Finset.sum_subset (fun m hm => by simp only [Finset.mem_union]; tauto)
      (fun m _ hm => hS₁ m hm)
  rw [e1, e2, Finset.smul_sum]
  exact Finset.sum_congr rfl fun m _ => seeleyTV_smul a b δ c g m p

/-- The Seeley extension operator, as a real linear map. -/
def seeleyEVLin (a b : ℕ → ℝ) (δ : ℝ) (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) :
    (X × ℝ → ℂ) →ₗ[ℝ] (X × ℝ → ℂ) where
  toFun := seeleyEV a b δ
  map_add' g₁ g₂ := by
    funext p
    by_cases hp : 0 ≤ p.2
    · rw [Pi.add_apply, seeleyEV_of_nonneg a b δ (g₁ + g₂) hp,
        seeleyEV_of_nonneg a b δ g₁ hp, seeleyEV_of_nonneg a b δ g₂ hp, Pi.add_apply]
    · have hp' : p.2 < 0 := lt_of_not_ge hp
      rw [Pi.add_apply, seeleyEV_of_neg a b δ (g₁ + g₂) hp', seeleyEV_of_neg a b δ g₁ hp',
        seeleyEV_of_neg a b δ g₂ hp', seeleySumV_add hb hbT δ g₁ g₂ hp']
  map_smul' c g := by
    funext p
    by_cases hp : 0 ≤ p.2
    · rw [Pi.smul_apply, seeleyEV_of_nonneg a b δ (c • g) hp, seeleyEV_of_nonneg a b δ g hp,
        RingHom.id_apply, Pi.smul_apply]
    · have hp' : p.2 < 0 := lt_of_not_ge hp
      rw [Pi.smul_apply, seeleyEV_of_neg a b δ (c • g) hp', seeleyEV_of_neg a b δ g hp',
        RingHom.id_apply, seeleySumV_smul hb hbT δ c g hp']

lemma seeleyEVLin_apply (a b : ℕ → ℝ) (δ : ℝ) (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (g : X × ℝ → ℂ) :
    seeleyEVLin a b δ hb hbT g = seeleyEV a b δ g := rfl

end Work.NN.Final
