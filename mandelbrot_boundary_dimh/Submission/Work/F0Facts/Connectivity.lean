import Mathlib
import Submission.Work.F0Facts.Basic
import Submission.Work.F0Facts.Petal
import Submission.Work.F0Facts.RealOrbit
import Submission.Work.F0Facts.sqrt_pre_connected
import Submission.Work.F0Facts.eventually_mem_petal

/-!
# The parabolic basin of `f₀` is connected

The basin `Basin` is invariant under `f₀` backwards (`f0 ⁻¹' Basin = Basin`), contains the
critical value `-1/4`, and the preimage of the connected component `C` of `-1/4` is connected
because `f₀(z) = (z + 1/2)² - 1/4` makes it the preimage of a connected set under the squaring
map (`sqrt_pre_connected`).  Hence `f0 ⁻¹' C = C`, and since every orbit in the basin eventually
enters the petal, which is connected and meets `C`, the basin is exactly `C`.
-/

namespace Work.F0Facts

open MandelDim Filter Set Metric Topology
open scoped Topology

noncomputable section

/-- The connected component of the critical value `-1/4` in the parabolic basin. -/
def C : Set ℂ := connectedComponentIn Basin (-1/4)

lemma mem_Basin_neg_quarter : (-1/4 : ℂ) ∈ Basin := by
  simpa using ofReal_mem_Basin (t := -1/4) (by norm_num) (by norm_num)

lemma isOpen_C : IsOpen C := isOpen_Basin.connectedComponentIn

lemma isPreconnected_C : IsPreconnected C := isPreconnected_connectedComponentIn

lemma C_subset_Basin : C ⊆ Basin := connectedComponentIn_subset _ _

lemma neg_quarter_mem_C : (-1/4 : ℂ) ∈ C := mem_connectedComponentIn mem_Basin_neg_quarter

lemma isConnected_C : IsConnected C := ⟨⟨-1/4, neg_quarter_mem_C⟩, isPreconnected_C⟩

/-- Every real point of `(-1/2, 0)` lies in the component `C`. -/
lemma ofReal_Ioo_mem_C {t : ℝ} (ht1 : -(1 / 2) < t) (ht2 : t < 0) : (t : ℂ) ∈ C := by
  have hsub : ((fun s : ℝ => (s : ℂ)) '' Set.Ioo (-(1 / 2)) 0) ⊆ C := by
    refine IsPreconnected.subset_connectedComponentIn ?_ ?_ ?_
    · exact isPreconnected_Ioo.image _ Complex.continuous_ofReal.continuousOn
    · exact ⟨(-1/4 : ℝ), ⟨by norm_num, by norm_num⟩, by norm_num⟩
    · rintro x ⟨s, hs, rfl⟩
      exact ofReal_mem_Basin (le_of_lt hs.1) hs.2
  exact hsub ⟨t, ⟨ht1, ht2⟩, rfl⟩

/-! ## `f₀ ⁻¹' C` is connected -/

lemma isConnected_preimage_C : IsConnected (f0 ⁻¹' C) := by
  have hVimg : {w : ℂ | w - 1/4 ∈ C} = (fun c : ℂ => c + 1/4) '' C := by
    ext w
    constructor
    · intro hw; exact ⟨w - 1/4, hw, by ring⟩
    · rintro ⟨c, hc, rfl⟩; simpa using hc
  have hVo : IsOpen {w : ℂ | w - 1/4 ∈ C} :=
    isOpen_C.preimage (continuous_id.sub continuous_const)
  have hVc : IsConnected {w : ℂ | w - 1/4 ∈ C} := by
    rw [hVimg]
    exact isConnected_C.image _ (continuous_id.add continuous_const).continuousOn
  have hV0 : (0 : ℂ) ∈ {w : ℂ | w - 1/4 ∈ C} := by
    show (0 : ℂ) - 1/4 ∈ C
    rw [show (0 : ℂ) - 1/4 = -1/4 by norm_num]
    exact neg_quarter_mem_C
  have hA : IsConnected {y : ℂ | y ^ 2 ∈ {w : ℂ | w - 1/4 ∈ C}} :=
    sqrt_pre_connected hVo hVc hV0
  have heq : f0 ⁻¹' C = (fun y : ℂ => y - 1/2) '' {y : ℂ | y ^ 2 ∈ {w : ℂ | w - 1/4 ∈ C}} := by
    ext z
    constructor
    · intro hz
      refine ⟨z + 1/2, ?_, by ring⟩
      show (z + 1/2) ^ 2 - 1/4 ∈ C
      have h : f0 z = (z + 1/2) ^ 2 - 1/4 := by rw [f0_eq]; ring
      rw [← h]; exact hz
    · rintro ⟨y, hy, rfl⟩
      show f0 (y - 1/2) ∈ C
      have h : f0 (y - 1/2) = y ^ 2 - 1/4 := by rw [f0_eq]; ring
      rw [h]; exact hy
  rw [heq]
  exact hA.image _ (continuous_id.sub continuous_const).continuousOn

/-- `f₀ ⁻¹' C ⊆ C`: the preimage of the component is connected and contains the critical value
`-1/4` (since `f₀(-1/4) = -3/16 ∈ C`). -/
lemma preimage_C_subset_C : f0 ⁻¹' C ⊆ C := by
  have hconn : IsPreconnected (f0 ⁻¹' C) := isConnected_preimage_C.isPreconnected
  have hsub : f0 ⁻¹' C ⊆ Basin := by
    intro z hz
    rw [← basin_preimage]
    exact Set.preimage_mono C_subset_Basin hz
  have hmem : (-1/4 : ℂ) ∈ f0 ⁻¹' C := by
    show f0 (-1/4) ∈ C
    have h : f0 (-1/4) = -3/16 := by rw [f0_eq]; norm_num
    rw [h]
    simpa using ofReal_Ioo_mem_C (t := -3/16) (by norm_num) (by norm_num)
  exact IsPreconnected.subset_connectedComponentIn hconn hmem hsub

lemma neg_half_mem_C : (-1/2 : ℂ) ∈ C := by
  have h : (-1/2 : ℂ) ∈ f0 ⁻¹' C := by
    show f0 (-1/2) ∈ C
    have h' : f0 (-1/2) = -1/4 := by rw [f0_eq]; norm_num
    rw [h']
    exact neg_quarter_mem_C
  exact preimage_C_subset_C h

/-- `C` is forward invariant. -/
lemma image_C_subset_C : f0 '' C ⊆ C := by
  have hconn : IsPreconnected (f0 '' C) :=
    isPreconnected_C.image _ continuous_f0.continuousOn
  have hsub : f0 '' C ⊆ Basin := by
    rintro x ⟨z, hz, rfl⟩
    exact f0_mem_Basin (C_subset_Basin hz)
  have hmem : (-1/4 : ℂ) ∈ f0 '' C := ⟨-1/2, neg_half_mem_C, by rw [f0_eq]; norm_num⟩
  exact IsPreconnected.subset_connectedComponentIn hconn hmem hsub

lemma preimage_C_eq_C : f0 ⁻¹' C = C :=
  Subset.antisymm preimage_C_subset_C (fun x hx => image_C_subset_C ⟨x, hx, rfl⟩)

lemma mem_C_of_iterate_mem_C {z : ℂ} : ∀ n : ℕ, f0^[n] z ∈ C → z ∈ C := by
  intro n
  induction n with
  | zero => intro h; simpa using h
  | succ n ih =>
    intro h
    rw [Function.iterate_succ_apply'] at h
    exact ih (preimage_C_subset_C h)

/-! ## The petal meets `C` -/

lemma exists_petal_subset_C :
    ∃ r M : ℝ, 0 < r ∧ 1 / r < M ∧ Work.FatouCoord.Petal r M ⊆ C := by
  obtain ⟨r, M, hr, hM, h1rM, hsub, hconn, hint⟩ := exists_petal_data
  have hmono : 0 < M := lt_trans (by positivity : (0:ℝ) < 1/r) h1rM
  have hminpos : 0 < min (1 / M) (1 / 2) := lt_min (by positivity) (by norm_num)
  set t : ℝ := -(min (1 / M) (1 / 2)) / 2 with ht
  have htneg : t < 0 := by rw [ht]; linarith
  have htP : (t : ℂ) ∈ Work.FatouCoord.Petal r M := by
    refine hint t ?_ htneg
    rw [ht]
    have hle : min (1 / M) (1 / 2) ≤ 1 / M := min_le_left _ _
    linarith
  have htC : (t : ℂ) ∈ C := by
    refine ofReal_Ioo_mem_C ?_ htneg
    rw [ht]
    have hle : min (1 / M) (1 / 2) ≤ 1 / 2 := min_le_right _ _
    linarith
  refine ⟨r, M, hr, h1rM, ?_⟩
  have hcomp : connectedComponentIn Basin (-1/4) = connectedComponentIn Basin t :=
    connectedComponentIn_eq htC
  intro x hx
  have hx' : x ∈ connectedComponentIn Basin t :=
    IsPreconnected.subset_connectedComponentIn hconn.isPreconnected htP hsub hx
  rw [show C = connectedComponentIn Basin t from hcomp]
  exact hx'

/-! ## The basin is connected -/

lemma basin_subset_C : Basin ⊆ C := by
  intro z hz
  have hzB : z ∈ Basin := hz
  obtain ⟨r, M, hr, h1rM, hpet⟩ := exists_petal_subset_C
  obtain ⟨U, hU, hmap, hunif⟩ := hz
  have hzU : z ∈ U := mem_of_mem_nhds hU
  have hconv : Tendsto (fun n : ℕ => f0^[n] z) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    rw [Metric.tendstoUniformlyOn_iff] at hunif
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hunif ε hε)
    refine ⟨N, fun n hn => ?_⟩
    have h : dist 0 (f0^[n] z) < ε := hN n hn z hzU
    rwa [dist_comm] at h
  obtain ⟨N, hN⟩ := eventually_mem_petal hr h1rM hconv (f0_iterate_ne_zero hzB)
  exact mem_C_of_iterate_mem_C N (hpet hN)

theorem isConnected_Basin : IsConnected Basin := by
  have h : C = Basin := Subset.antisymm C_subset_Basin basin_subset_C
  rw [← h]
  exact isConnected_C

end
end Work.F0Facts
