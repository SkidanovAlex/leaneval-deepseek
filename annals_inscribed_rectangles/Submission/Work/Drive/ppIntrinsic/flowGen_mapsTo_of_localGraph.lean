import Mathlib
import Submission.Work.Drive.ppIntrinsic.FlowGen
import Submission.Work.Drive.BoxParityAux
import Submission.Work.Drive.ManifoldParity.GraphMap
import Submission.Work.Drive.ManifoldParity.GraphFlow
import Submission.Work.Drive.ManifoldParity.GraphFDeriv
import Submission.Work.Drive.interior_unitBox
import Submission.Work.Drive.crossing_of_deriv_ne_zero
import Submission.Work.Drive.exists_local_normalForm

/-!
# The flow of a field tangent to a locally-graph-like closed set stays on the set (in the box)

`Z ⊆ ℝ^{m+1}` is closed and, near every point of `Z ∩ [0,1]^{m+1}`, a graph of a smooth map `η` over
one coordinate `i` (`hgra`).  The smooth compactly supported field `V` is *parallel* to that graph
at every point of `Z ∩ [0,1]^{m+1}` (`hVpar`), and transversal to the face of the box at every
boundary point of `Z` in the box (`hface`).

Then the flow line of `V` through a point of `Z` which stays in the closed box on the time interval
between `0` and `t` is again in `Z` at time `t`.

The proof is the standard one: the set of times up to which the flow line stays on `Z` is closed and
non-empty, so it has a largest element `T`; if `T < t` one shows that the flow line stays on `Z` for
a short time past `T` as well.  On the *side of the motion* the local graph points stay in the box
(this is where the sign of the velocity and `hface` are used), so the Grönwall argument
`eq_graphMap_of_tangent_flow_right` applies to the local graph.
-/

namespace Work.Drive.ppIntrinsic

open scoped ContDiff Topology
open Set Filter

noncomputable section

variable {m : ℕ}

/-! ## Basic facts about a local graph `u ↦ u • eᵢ + η u` -/

/-- A point of the graph of `η` over the coordinate `i` lies in `Z`, whenever it lies in the chart
region `U` where `Z` is described by that graph. -/
theorem graphMap_mem_of_prop {Z : Set (Amb m)} {i : Fin (m + 1)} {U : Set (Amb m)}
    {η : ℝ → Amb m} (hηi : ∀ u : ℝ, η u i = 0)
    (hprop : ∀ y ∈ U, (y ∈ Z ↔ y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i)))
    {u : ℝ} (hu : ManifoldParity.graphMap i η u ∈ U) : ManifoldParity.graphMap i η u ∈ Z := by
  rw [hprop _ hu, ManifoldParity.graphMap_apply_i hηi]
  rfl

/-- A point of `Z` inside the chart region `U` is a graph point. -/
theorem eq_graphMap_of_mem_prop {Z : Set (Amb m)} {i : Fin (m + 1)} {U : Set (Amb m)}
    {η : ℝ → Amb m}
    (hprop : ∀ y ∈ U, (y ∈ Z ↔ y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i)))
    {y : Amb m} (hyU : y ∈ U) (hyZ : y ∈ Z) : y = ManifoldParity.graphMap i η (y i) :=
  (hprop y hyU).mp hyZ

/-- The `i`-th component of `fderiv η u 1` vanishes when `η` takes its values in `{x | x i = 0}`. -/
theorem fderiv_apply_one_apply_i {i : Fin (m + 1)} {η : ℝ → Amb m} {u : ℝ}
    (hη : DifferentiableAt ℝ η u) (hηi : ∀ t : ℝ, η t i = 0) :
    ((fderiv ℝ η u) 1) i = 0 := by
  have hcomp : HasFDerivAt (fun t : ℝ => η t i) ((Work.Drive.coordL i).comp (fderiv ℝ η u)) u :=
    (Work.Drive.coordL_hasFDerivAt i (η u)).comp u hη.hasFDerivAt
  have hfun : (fun t : ℝ => η t i) = Function.const ℝ (0 : ℝ) := funext hηi
  have h1 : fderiv ℝ (fun t : ℝ => η t i) u = (Work.Drive.coordL i).comp (fderiv ℝ η u) :=
    hcomp.fderiv
  have h2 : fderiv ℝ (fun t : ℝ => η t i) u = 0 := by
    rw [hfun, fderiv_const]
    simp
  have hzero : (Work.Drive.coordL i).comp (fderiv ℝ η u) = 0 := by
    rw [← h1, h2]
  have h3 := congrArg (fun (f : ℝ →L[ℝ] ℝ) => f 1) hzero
  simpa [ContinuousLinearMap.comp_apply, Work.Drive.coordL_apply] using h3

/-- The derivative of the graph map, applied to a scalar. -/
theorem fderiv_graphMap_apply {i : Fin (m + 1)} {η : ℝ → Amb m} {u : ℝ}
    (hη : DifferentiableAt ℝ η u) (w : ℝ) :
    fderiv ℝ (ManifoldParity.graphMap i η) u w =
      w • EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η u) w := by
  have h := ManifoldParity.hasFDerivAt_graphMap (η := η) (i := i) hη.hasFDerivAt
  rw [h.fderiv]
  simp [ContinuousLinearMap.toSpanSingleton_apply]

/-- The `i`-th component of the tangent vector `c • (eᵢ + dη 1)` of the graph of `η` is `c`. -/
theorem smul_par_apply_i {i : Fin (m + 1)} {η : ℝ → Amb m} {u c : ℝ}
    (hη : DifferentiableAt ℝ η u) (hηi : ∀ t : ℝ, η t i = 0) :
    (c • (EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η u) 1)) i = c := by
  rw [PiLp.smul_apply, PiLp.add_apply, PiLp.single_apply, if_pos rfl,
    fderiv_apply_one_apply_i hη hηi]
  ring

/-- **Tangency of `V` to the graph of `η`.** If `V` is parallel to the graph at every point of
`Z` in the box (`hVpar`), then at a graph point `g u ∈ Z ∩ [0,1]^{m+1}` the vector `V (g u)` is the
derivative of the graph map applied to its own `i`-th component. -/
theorem graphMap_tangency {Z : Set (Amb m)} {i : Fin (m + 1)}
    {U : Set (Amb m)} {η : ℝ → Amb m} {V : Amb m → Amb m}
    (hU : IsOpen U) (hηcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (hηi : ∀ u : ℝ, η u i = 0)
    (hprop : ∀ y ∈ U, (y ∈ Z ↔ y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i)))
    (hVpar : ∀ x ∈ Z ∩ Submission.Drive.unitBox m,
      ∀ (j : Fin (m + 1)) (W : Set (Amb m)) (ζ : ℝ → Amb m),
      IsOpen W → x ∈ W → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ → (∀ t : ℝ, ζ t j = 0) →
      (∀ y ∈ W, (y ∈ Z ↔ y = (y j) • EuclideanSpace.single j (1 : ℝ) + ζ (y j))) →
      ∃ c : ℝ, c ≠ 0 ∧ V x = c • (EuclideanSpace.single j (1 : ℝ) + (fderiv ℝ ζ (x j)) (1 : ℝ)))
    {u : ℝ} (huU : ManifoldParity.graphMap i η u ∈ U)
    (huZ : ManifoldParity.graphMap i η u ∈ Z)
    (hubox : ManifoldParity.graphMap i η u ∈ Submission.Drive.unitBox m) :
    V (ManifoldParity.graphMap i η u) =
      fderiv ℝ (ManifoldParity.graphMap i η) u ((V (ManifoldParity.graphMap i η u)) i) := by
  obtain ⟨c, hc, hVeq⟩ :=
    hVpar (ManifoldParity.graphMap i η u) ⟨huZ, hubox⟩ i U η hU huU hηcd hηi hprop
  have hηd : DifferentiableAt ℝ η u := (hηcd.differentiable (by simp)).differentiableAt
  have hgu : (ManifoldParity.graphMap i η u) i = u := ManifoldParity.graphMap_apply_i hηi u
  have hpar : (c • (EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η u) 1)) i = c :=
    smul_par_apply_i hηd hηi
  rw [hVeq, hgu, hpar, fderiv_graphMap_apply hηd]
  rw [smul_add, ← map_smul]
  simp

/-! ## Sign lemmas for a differentiable function on one side of a point -/

theorem exists_mul_side_nonneg {ψ : ℝ → ℝ} {u₀ w c e : ℝ} (hψ : HasDerivAt ψ w u₀)
    (h : 0 < e * (c * w)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : ℝ, |u - u₀| < ρ → 0 ≤ (u - u₀) * c → 0 ≤ e * (ψ u - ψ u₀) := by
  have hcw : c * w ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at h
    exact absurd h (lt_irrefl 0)
  have hc : c ≠ 0 := fun h0 => hcw (by rw [h0, zero_mul])
  have hw : w ≠ 0 := fun h0 => hcw (by rw [h0, mul_zero])
  have he_pos : 0 < c * w → 0 < e := by
    intro hd
    rcases mul_pos_iff.mp h with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact h1
    · exact absurd h2 (not_lt.mpr (le_of_lt hd))
  have he_neg : c * w < 0 → e < 0 := by
    intro hd
    rcases mul_pos_iff.mp h with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact absurd h2 (not_lt.mpr (le_of_lt hd))
    · exact h1
  have hψ' : HasDerivAt ψ w (0 + u₀) := by simpa using hψ
  have hshift : HasDerivAt (fun s : ℝ => ψ (s + u₀)) w 0 := hψ'.comp_add_const 0 u₀
  have reduce : ∀ (δ : ℝ), 0 < δ →
      (∀ s : ℝ, 0 < s * c → |s| < δ → 0 ≤ e * (ψ (s + u₀) - ψ u₀)) →
      ∀ u : ℝ, |u - u₀| < δ → 0 ≤ (u - u₀) * c → 0 ≤ e * (ψ u - ψ u₀) := by
    intro δ hδ hside u hu huc
    rcases eq_or_ne u u₀ with rfl | hne
    · simp
    · have hs : 0 < (u - u₀) * c :=
        lt_of_le_of_ne huc (Ne.symm (mul_ne_zero (sub_ne_zero.mpr hne) hc))
      have h1 := hside (u - u₀) hs hu
      rwa [sub_add_cancel] at h1
  rcases lt_or_gt_of_ne hc with hclt | hcgt
  · -- c < 0 : the side is s < 0
    rcases lt_or_gt_of_ne hw with hwlt | hwgt
    · -- w < 0, e > 0 : ψ increases to the left of u₀
      obtain ⟨δ, hδ, -, hP2, -⟩ := Work.Drive.scalar_neg hshift hwlt
      refine ⟨δ, hδ, reduce δ hδ (fun s hs hsd => ?_)⟩
      have hslt : s < 0 := by
        rcases mul_pos_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd h2 (not_lt.mpr (le_of_lt hclt))
        · exact h1
      have hsmem : s ∈ Set.Ioo (-δ) 0 := by
        rw [abs_lt] at hsd
        exact ⟨hsd.1, hslt⟩
      have h1 := hP2 s hsmem
      rw [zero_add] at h1
      have h2 : 0 < ψ (s + u₀) - ψ u₀ := by linarith
      exact le_of_lt (mul_pos (he_pos (mul_pos_of_neg_of_neg hclt hwlt)) h2)
    · -- w > 0, e < 0 : ψ decreases to the left of u₀
      obtain ⟨δ, hδ, -, hP2, -⟩ := Work.Drive.scalar_pos hshift hwgt
      refine ⟨δ, hδ, reduce δ hδ (fun s hs hsd => ?_)⟩
      have hslt : s < 0 := by
        rcases mul_pos_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd h2 (not_lt.mpr (le_of_lt hclt))
        · exact h1
      have hsmem : s ∈ Set.Ioo (-δ) 0 := by
        rw [abs_lt] at hsd
        exact ⟨hsd.1, hslt⟩
      have h1 := hP2 s hsmem
      rw [zero_add] at h1
      have h2 : ψ (s + u₀) - ψ u₀ < 0 := by linarith
      exact le_of_lt (mul_pos_of_neg_of_neg (he_neg (mul_neg_of_neg_of_pos hclt hwgt)) h2)
  · -- c > 0 : the side is s > 0
    rcases lt_or_gt_of_ne hw with hwlt | hwgt
    · -- w < 0, e < 0 : ψ decreases to the right of u₀
      obtain ⟨δ, hδ, hP1, -, -⟩ := Work.Drive.scalar_neg hshift hwlt
      refine ⟨δ, hδ, reduce δ hδ (fun s hs hsd => ?_)⟩
      have hsgt : 0 < s := by
        rcases mul_pos_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h1
        · exact absurd h2 (not_lt.mpr (le_of_lt hcgt))
      have hsmem : s ∈ Set.Ioo (0 : ℝ) δ := by
        rw [abs_lt] at hsd
        exact ⟨hsgt, hsd.2⟩
      have h1 := hP1 s hsmem
      rw [zero_add] at h1
      have h2 : ψ (s + u₀) - ψ u₀ < 0 := by linarith
      exact le_of_lt (mul_pos_of_neg_of_neg (he_neg (mul_neg_of_pos_of_neg hcgt hwlt)) h2)
    · -- w > 0, e > 0 : ψ increases to the right of u₀
      obtain ⟨δ, hδ, hP1, -, -⟩ := Work.Drive.scalar_pos hshift hwgt
      refine ⟨δ, hδ, reduce δ hδ (fun s hs hsd => ?_)⟩
      have hsgt : 0 < s := by
        rcases mul_pos_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h1
        · exact absurd h2 (not_lt.mpr (le_of_lt hcgt))
      have hsmem : s ∈ Set.Ioo (0 : ℝ) δ := by
        rw [abs_lt] at hsd
        exact ⟨hsgt, hsd.2⟩
      have h1 := hP1 s hsmem
      rw [zero_add] at h1
      have h2 : 0 < ψ (s + u₀) - ψ u₀ := by linarith
      exact le_of_lt (mul_pos (he_pos (mul_pos hcgt hwgt)) h2)

theorem sign_deriv_of_box_right {g : ℝ → ℝ} {c T t : ℝ} (hg : HasDerivAt g c T) (hc : c ≠ 0)
    (hbox : ∀ s ∈ Set.Ioc T t, g s ∈ Set.Icc (0 : ℝ) 1) (hTt : T < t) :
    (g T = 0 → 0 < c) ∧ (g T = 1 → c < 0) := by
  have hgt : 0 < t - T := by linarith
  have hg' : HasDerivAt g c (0 + T) := by simpa using hg
  have hshift : HasDerivAt (fun s : ℝ => g (s + T)) c 0 := hg'.comp_add_const 0 T
  constructor
  · intro h0
    by_contra hcon
    have hclt : c < 0 := lt_of_le_of_ne (not_lt.mp hcon) hc
    obtain ⟨δ, hδ, hP1, -, -⟩ := Work.Drive.scalar_neg hshift hclt
    obtain ⟨s, hs1, hs2⟩ : ∃ s : ℝ, 0 < s ∧ s < min δ (t - T) :=
      ⟨min δ (t - T) / 2, by linarith [lt_min hδ hgt], by linarith [lt_min hδ hgt]⟩
    have hsmem : s ∈ Set.Ioo (0 : ℝ) δ := ⟨hs1, lt_of_lt_of_le hs2 (min_le_left _ _)⟩
    have hlt := hP1 s hsmem
    have hb := hbox (s + T) ⟨by linarith, by linarith [hs2, min_le_right δ (t - T)]⟩
    rw [zero_add, h0] at hlt
    linarith [hb.1]
  · intro h1
    by_contra hcon
    have hcgt : 0 < c := lt_of_le_of_ne (not_lt.mp hcon) hc.symm
    obtain ⟨δ, hδ, hP1, -, -⟩ := Work.Drive.scalar_pos hshift hcgt
    obtain ⟨s, hs1, hs2⟩ : ∃ s : ℝ, 0 < s ∧ s < min δ (t - T) :=
      ⟨min δ (t - T) / 2, by linarith [lt_min hδ hgt], by linarith [lt_min hδ hgt]⟩
    have hsmem : s ∈ Set.Ioo (0 : ℝ) δ := ⟨hs1, lt_of_lt_of_le hs2 (min_le_left _ _)⟩
    have hlt := hP1 s hsmem
    have hb := hbox (s + T) ⟨by linarith, by linarith [hs2, min_le_right δ (t - T)]⟩
    rw [zero_add, h1] at hlt
    linarith [hb.2]

theorem exists_forall_mul_nonneg {ψ : ℝ → ℝ} {c : ℝ} (h : HasDerivAt ψ c 0) (hc : c ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Set.Icc (0 : ℝ) ε, 0 ≤ (ψ s - ψ 0) * c := by
  rcases lt_or_gt_of_ne hc with hclt | hcgt
  · obtain ⟨δ, hδ, hP1, -, -⟩ := Work.Drive.scalar_neg h hclt
    refine ⟨δ / 2, by linarith, fun s hs => ?_⟩
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0]
      simp
    · have h1 := hP1 s ⟨h0, by linarith [hs.2]⟩
      have h2 : ψ s - ψ 0 < 0 := by linarith
      exact le_of_lt (mul_pos_of_neg_of_neg h2 hclt)
  · obtain ⟨δ, hδ, hP1, -, -⟩ := Work.Drive.scalar_pos h hcgt
    refine ⟨δ / 2, by linarith, fun s hs => ?_⟩
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0]
      simp
    · have h1 := hP1 s ⟨h0, by linarith [hs.2]⟩
      exact le_of_lt (mul_pos (by linarith) hcgt)

/-! ## Local forward invariance of the graph -/

/-- **The flow line of a field tangent to the graph stays on the graph (forward in time), as long
as its coordinate stays on the side of `q` on which the graph points are known to be in the box.**

This is a packaging of `Work.Drive.ManifoldParity.eq_graphMap_of_tangent_flow_right`: we only need
the tangency identity and the box membership of the graph points along the flow line. -/
theorem local_forward_mem_of_graph {Z : Set (Amb m)} {V : Amb m → Amb m} {L : NNReal}
    {i : Fin (m + 1)} {η : ℝ → Amb m} {γ : ℝ → Amb m} {q : Amb m} {c ρ ε : ℝ}
    (hL : LipschitzWith L V) (hγ : ∀ s : ℝ, HasDerivAt γ (V (γ s)) s) (hγq : γ 0 = q)
    (hηcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (hgq : ManifoldParity.graphMap i η (q i) = q) (_hc : c ≠ 0)
    (hε : 0 < ε) (_hρ : 0 < ρ)
    (hmem : ∀ s ∈ Set.Icc (0 : ℝ) ε, |(γ s) i - q i| < ρ ∧ 0 ≤ ((γ s) i - q i) * c)
    (htan : ∀ u : ℝ, |u - q i| < ρ → 0 ≤ (u - q i) * c →
      V (ManifoldParity.graphMap i η u) =
        fderiv ℝ (ManifoldParity.graphMap i η) u ((V (ManifoldParity.graphMap i η u)) i))
    (hZ : ∀ u : ℝ, |u - q i| < ρ → 0 ≤ (u - q i) * c → ManifoldParity.graphMap i η u ∈ Z) :
    ∀ s ∈ Set.Icc (0 : ℝ) ε, γ s ∈ Z := by
  have hηd : Differentiable ℝ η := hηcd.differentiable (by simp)
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ u ∈ Set.Icc (q i - ρ) (q i + ρ),
      ‖fderiv ℝ (ManifoldParity.graphMap i η) u‖ ≤ C := by
    refine IsCompact.exists_bound_of_continuousOn isCompact_Icc ?_
    exact ((ManifoldParity.contDiff_graphMap hηcd).continuous_fderiv (by simp)).continuousOn
  have hC' : ∀ s ∈ Set.Icc (0 : ℝ) ε,
      ‖fderiv ℝ (ManifoldParity.graphMap i η) ((γ s) i)‖ ≤ C := by
    intro s hs
    refine hC _ ?_
    rw [Set.mem_Icc]
    have h := abs_lt.mp (hmem s hs).1
    exact ⟨by linarith, by linarith⟩
  have htan' : ∀ s ∈ Set.Icc (0 : ℝ) ε,
      V (ManifoldParity.graphMap i η ((γ s) i)) =
        fderiv ℝ (ManifoldParity.graphMap i η) ((γ s) i)
          ((V (ManifoldParity.graphMap i η ((γ s) i))) i) :=
    fun s hs => htan _ (hmem s hs).1 (hmem s hs).2
  have hinit : γ 0 = ManifoldParity.graphMap i η ((γ 0) i) := by
    rw [hγq]
    exact hgq.symm
  have hgraph := ManifoldParity.eq_graphMap_of_tangent_flow_right (i := i) (ε := ε)
    hL hγ hηd hε hC' htan' hinit
  intro s hs
  rw [hgraph s hs]
  exact hZ _ (hmem s hs).1 (hmem s hs).2

/-! ## The local graph points on the side of the motion lie in the box -/

/-- **The points of the local graph on the side of the motion lie in the box.**

`q = γ T ∈ Z ∩ [0,1]^{m+1}` lies in the chart region `U` where `Z` is the graph of `η` over the
coordinate `i`, and `V q = c • (eᵢ + dη (q i) 1)` with `c ≠ 0` (`hVeq`).  The flow line `γ` stays in
the box on `(T, t]` (`hbox`, `hTt`), and at a boundary point of the box the field is transversal to
the face (`hface`).

Then the graph points `graphMap i η u` for `u` near `q i` **on the side to which the flow line
moves** (i.e. `0 ≤ (u - q i) * c`) lie in `U` and in the box. -/
theorem graphMap_mem_of_side {Z : Set (Amb m)} {i : Fin (m + 1)} {U : Set (Amb m)}
    {η : ℝ → Amb m} {V : Amb m → Amb m} {γ : ℝ → Amb m} {T t c : ℝ}
    (hU : IsOpen U) (hηcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η) (hηi : ∀ u : ℝ, η u i = 0)
    (hprop : ∀ y ∈ U, (y ∈ Z ↔ y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i)))
    (hqU : γ T ∈ U) (hqZ : γ T ∈ Z) (hqbox : γ T ∈ Submission.Drive.unitBox m)
    (hγ : ∀ s : ℝ, HasDerivAt γ (V (γ s)) s)
    (hface : ∀ b ∈ Z ∩ Submission.Drive.unitBoxBdry m,
        ∃ j : Fin (m + 1), (b j = 0 ∨ b j = 1) ∧
          (∀ l : Fin (m + 1), l ≠ j → b l ∈ Set.Ioo (0 : ℝ) 1) ∧ V b j ≠ 0)
    (hbox : ∀ s ∈ Set.Ioc T t, γ s ∈ Submission.Drive.unitBox m) (hTt : T < t)
    (hVeq : V (γ T) = c • (EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η ((γ T) i)) (1 : ℝ)))
    (hc : c ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : ℝ, |u - (γ T) i| < ρ → 0 ≤ (u - (γ T) i) * c →
      ManifoldParity.graphMap i η u ∈ U ∧
        ManifoldParity.graphMap i η u ∈ Submission.Drive.unitBox m := by
  classical
  have hηd : ∀ u : ℝ, DifferentiableAt ℝ η u :=
    fun u => (hηcd.differentiable (by simp)).differentiableAt
  have hVqi : (V (γ T)) i = c := by
    rw [hVeq]
    exact smul_par_apply_i (hηd _) hηi
  have hqgraph : γ T = ManifoldParity.graphMap i η ((γ T) i) :=
    eq_graphMap_of_mem_prop hprop hqU hqZ
  have hηq : ∀ j : Fin (m + 1), j ≠ i → η ((γ T) i) j = (γ T) j := by
    intro j hj
    have h := congrArg (fun x : Amb m => x j) hqgraph
    simpa [ManifoldParity.graphMap_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, hj,
      smul_zero, zero_add] using h.symm
  have hcoord : ∀ j : Fin (m + 1),
      HasDerivAt (fun s : ℝ => (γ (T + s)) j) ((V (γ T)) j) 0 := by
    intro j
    have h1 : HasDerivAt (fun s : ℝ => γ s j) ((V (γ T)) j) (T + 0) := by
      simpa using Work.Drive.hasDerivAt_apply (hγ T) j
    have h2 : HasDerivAt (fun s : ℝ => T + s) (1 : ℝ) 0 :=
      (hasDerivAt_id (0 : ℝ)).const_add T
    have h3 := h1.comp 0 h2
    simpa [Function.comp_def, mul_one] using h3
  have hηc : Continuous η := hηcd.continuous
  have hUnear : ∀ᶠ u in 𝓝 ((γ T) i), ManifoldParity.graphMap i η u ∈ U :=
    (hU.preimage (ManifoldParity.continuous_graphMap hηc)).mem_nhds
      (by rw [Set.mem_preimage, ← hqgraph]; exact hqU)
  by_cases hint : γ T ∈ interior (Submission.Drive.unitBox m)
  · -- the point is in the interior of the box: both sides work
    have hAll : ∀ j : Fin (m + 1), (γ T) j ∈ Set.Ioo (0 : ℝ) 1 := by
      rw [Work.Drive.interior_unitBox m] at hint
      exact hint
    have hboxnear : ∀ᶠ u in 𝓝 ((γ T) i),
        ManifoldParity.graphMap i η u ∈ Submission.Drive.unitBox m := by
      show ∀ᶠ u in 𝓝 ((γ T) i), ∀ j : Fin (m + 1),
        (ManifoldParity.graphMap i η u) j ∈ Set.Icc (0 : ℝ) 1
      refine Filter.eventually_all.mpr (fun j => ?_)
      by_cases hji : j = i
      · filter_upwards [isOpen_Ioo.mem_nhds (hAll i)] with u hu
        rw [hji, ManifoldParity.graphMap_apply_i hηi]
        exact Set.Ioo_subset_Icc_self hu
      · have hmem : η ((γ T) i) j ∈ Set.Ioo (0 : ℝ) 1 := by
          rw [hηq j hji]
          exact hAll j
        filter_upwards [((isOpen_Ioo).preimage (by fun_prop : Continuous fun u : ℝ => η u j)
          ).mem_nhds hmem] with u hu
        simpa [ManifoldParity.graphMap_apply, PiLp.add_apply, PiLp.smul_apply,
          PiLp.single_apply, hji, smul_zero, zero_add] using Set.Ioo_subset_Icc_self hu
    obtain ⟨ρ, hρ, hρ'⟩ := Metric.eventually_nhds_iff.mp (hUnear.and hboxnear)
    exact ⟨ρ, hρ, fun u hu _ => hρ' (by rwa [Real.dist_eq])⟩
  · -- the point is on the boundary of the box
    have hqbdry : γ T ∈ Submission.Drive.unitBoxBdry m :=
      ⟨hqbox, Work.Drive.exists_coord_eq_zero_or_one_of_not_mem_interior hqbox hint⟩
    obtain ⟨k, hk01, hkother, hVk⟩ := hface (γ T) ⟨hqZ, hqbdry⟩
    -- the two-sided coordinates
    have htwo : ∀ᶠ u in 𝓝 ((γ T) i), ∀ j : Fin (m + 1), j ≠ i → j ≠ k →
        (ManifoldParity.graphMap i η u) j ∈ Set.Ioo (0 : ℝ) 1 := by
      refine Filter.eventually_all.mpr (fun j => ?_)
      by_cases hji : j = i
      · exact Filter.Eventually.of_forall (fun u h => absurd hji h)
      by_cases hjk : j = k
      · exact Filter.Eventually.of_forall (fun u _ h => absurd hjk h)
      · have hmem : η ((γ T) i) j ∈ Set.Ioo (0 : ℝ) 1 := by
          rw [hηq j hji]
          exact hkother j hjk
        filter_upwards [((isOpen_Ioo).preimage (by fun_prop : Continuous fun u : ℝ => η u j)
          ).mem_nhds hmem] with u hu
        exact fun _ _ => by
          simpa [ManifoldParity.graphMap_apply, PiLp.add_apply, PiLp.smul_apply,
            PiLp.single_apply, hji, smul_zero, zero_add] using hu
    obtain ⟨ρ₁, hρ₁, hρ₁'⟩ := Metric.eventually_nhds_iff.mp (hUnear.and htwo)
    -- the coordinate `i` of the graph is the parameter `u`
    have hi : ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : ℝ, |u - (γ T) i| < ρ → 0 ≤ (u - (γ T) i) * c →
        u ∈ Set.Icc (0 : ℝ) 1 := by
      by_cases hqi : (γ T) i ∈ Set.Ioo (0 : ℝ) 1
      · obtain ⟨ρ, hρ, hρ'⟩ := Metric.eventually_nhds_iff.mp
          (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hqi)
            (fun u hu => Set.Ioo_subset_Icc_self hu))
        exact ⟨ρ, hρ, fun u hu _ => hρ' (by rwa [Real.dist_eq])⟩
      · have hmem : (γ T) i ∈ Set.Icc (0 : ℝ) 1 := hqbox i
        have h01 : (γ T) i = 0 ∨ (γ T) i = 1 := by
          rcases eq_or_lt_of_le hmem.1 with h | h
          · exact Or.inl h.symm
          · exact Or.inr (le_antisymm hmem.2 (not_lt.mp (fun hlt => hqi ⟨h, hlt⟩)))
        have hcsign : ((γ T) i = 0 → 0 < c) ∧ ((γ T) i = 1 → c < 0) := by
          have hf : HasDerivAt (fun s : ℝ => (γ s) i) c T := by
            rw [← hVqi]
            exact Work.Drive.hasDerivAt_apply (hγ T) i
          have hb : ∀ s ∈ Set.Ioc T t, (γ s) i ∈ Set.Icc (0 : ℝ) 1 :=
            fun s hs => (hbox s hs) i
          simpa using sign_deriv_of_box_right hf hc hb hTt
        rcases h01 with h0 | h1
        · -- `(γ T) i = 0`: the velocity points to the right
          refine ⟨1, one_pos, fun u hu huc => ?_⟩
          have hcpos : 0 < c := hcsign.1 h0
          have hge : 0 ≤ u := by
            have := (mul_nonneg_iff_of_pos_right hcpos).mp (by simpa [h0] using huc)
            simpa using this
          have hlt : u < 1 := by
            have := (abs_lt.mp hu).2
            rwa [h0, sub_zero] at this
          exact ⟨hge, le_of_lt hlt⟩
        · -- `(γ T) i = 1`: the velocity points to the left
          refine ⟨1, one_pos, fun u hu huc => ?_⟩
          have hcneg : c < 0 := hcsign.2 h1
          have hle : u ≤ 1 := by
            have h : u - (γ T) i ≤ 0 := by
              by_contra hcon
              rw [not_le] at hcon
              have := mul_neg_of_pos_of_neg hcon hcneg
              linarith
            rw [h1] at h
            linarith
          have hgt : 0 < u := by
            have := (abs_lt.mp hu).1
            rw [h1] at this
            linarith
          exact ⟨le_of_lt hgt, hle⟩
    obtain ⟨ρ₂, hρ₂, hρ₂'⟩ := hi
    -- the coordinate `k` of the graph
    have hk : ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : ℝ, |u - (γ T) i| < ρ → 0 ≤ (u - (γ T) i) * c →
        (ManifoldParity.graphMap i η u) k ∈ Set.Icc (0 : ℝ) 1 := by
      by_cases hki : k = i
      · refine ⟨ρ₂, hρ₂, fun u hu huc => ?_⟩
        rw [hki, ManifoldParity.graphMap_apply_i hηi]
        exact hρ₂' u hu huc
      · -- the nontrivial case: the face coordinate differs from the chart coordinate
        set e : ℝ := if (γ T) k = 0 then 1 else -1 with hedef
        have hinward : 0 < e * (V (γ T) k) := by
          have hf : HasDerivAt (fun s : ℝ => (γ s) k) (V (γ T) k) T :=
            Work.Drive.hasDerivAt_apply (hγ T) k
          have hb : ∀ s ∈ Set.Ioc T t, (γ s) k ∈ Set.Icc (0 : ℝ) 1 :=
            fun s hs => (hbox s hs) k
          have hsgn := sign_deriv_of_box_right hf hVk hb hTt
          rcases hk01 with hk0 | hk1
          · have h0 : 0 < V (γ T) k := hsgn.1 hk0
            rw [hedef, if_pos hk0]
            simpa using h0
          · have h1 : V (γ T) k < 0 := hsgn.2 hk1
            rw [hedef, if_neg (by rw [hk1]; norm_num)]
            simpa using neg_pos.mpr h1
        have hderk : HasDerivAt (fun u : ℝ => η u k)
            (((fderiv ℝ η ((γ T) i)) 1) k) ((γ T) i) :=
          Work.Drive.hasDerivAt_apply ((hηd _).hasFDerivAt.hasDerivAt) k
        have hVk_eq : V (γ T) k = c * (((fderiv ℝ η ((γ T) i)) 1) k) := by
          rw [hVeq, PiLp.smul_apply]
          congr 1
          rw [PiLp.add_apply, PiLp.single_apply, if_neg hki]
          simp
        obtain ⟨ρ, hρ, hρside⟩ := exists_mul_side_nonneg hderk (by rw [← hVk_eq]; exact hinward)
        -- a two-sided bound for `η · k`
        obtain ⟨ρr, hρr, hρrv⟩ : ∃ ρr : ℝ, 0 < ρr ∧ ∀ u : ℝ, |u - (γ T) i| < ρr →
            η u k ∈ Set.Ioo ((γ T) k - 1) ((γ T) k + 1) := by
          refine Metric.eventually_nhds_iff.mp ?_
          have hmem : η ((γ T) i) k ∈ Set.Ioo ((γ T) k - 1) ((γ T) k + 1) := by
            rw [hηq k hki]
            exact ⟨by linarith, by linarith⟩
          exact ((isOpen_Ioo).preimage (by fun_prop : Continuous fun u : ℝ => η u k)).mem_nhds hmem
        refine ⟨min ρ ρr, lt_min hρ hρr, fun u hu huc => ?_⟩
        have huρ : |u - (γ T) i| < ρ := lt_of_lt_of_le hu (min_le_left _ _)
        have huρr : |u - (γ T) i| < ρr := lt_of_lt_of_le hu (min_le_right _ _)
        have hside := hρside u huρ huc
        rw [hηq k hki] at hside
        have h2 := hρrv u huρr
        have hgk : (ManifoldParity.graphMap i η u) k = η u k := by
          rw [ManifoldParity.graphMap_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply,
            if_neg hki]
          simp
        rw [hgk]
        rcases hk01 with hk0 | hk1
        · have he1 : e = 1 := by rw [hedef, if_pos hk0]
          rw [he1, one_mul] at hside
          have hge : (0 : ℝ) ≤ η u k := by linarith [hside, hk0]
          have hle : η u k ≤ 1 := by linarith [h2.2, hk0]
          exact ⟨hge, hle⟩
        · have he2 : e = -1 := by rw [hedef, if_neg (by rw [hk1]; norm_num)]
          rw [he2, neg_one_mul] at hside
          have hle : η u k ≤ 1 := by linarith [hside, hk1]
          have hge : (0 : ℝ) ≤ η u k := by linarith [h2.1, hk1]
          exact ⟨hge, hle⟩
    obtain ⟨ρ₃, hρ₃, hρ₃'⟩ := hk
    refine ⟨min ρ₁ (min ρ₂ ρ₃), lt_min hρ₁ (lt_min hρ₂ hρ₃), fun u hu huc => ?_⟩
    have hu1 : dist u ((γ T) i) < ρ₁ := by
      rw [Real.dist_eq]
      exact lt_of_lt_of_le hu (min_le_left _ _)
    have hu2 : |u - (γ T) i| < ρ₂ :=
      lt_of_lt_of_le hu (le_trans (min_le_right _ _) (min_le_left _ _))
    have hu3 : |u - (γ T) i| < ρ₃ :=
      lt_of_lt_of_le hu (le_trans (min_le_right _ _) (min_le_right _ _))
    refine ⟨(hρ₁' hu1).1, ?_⟩
    show ∀ j : Fin (m + 1), (ManifoldParity.graphMap i η u) j ∈ Set.Icc (0 : ℝ) 1
    intro j
    by_cases hji : j = i
    · rw [hji, ManifoldParity.graphMap_apply_i hηi]
      exact hρ₂' u hu2 huc
    by_cases hjk : j = k
    · rw [hjk]
      exact hρ₃' u hu3 huc
    · exact Set.Ioo_subset_Icc_self ((hρ₁' hu1).2 j hji hjk)
theorem flowGen_mapsTo_of_localGraph {m : ℕ} {Z : Set (Work.Drive.Amb m)} (hZ : IsClosed Z)
    (hgra : ∀ x ∈ Z ∩ Submission.Drive.unitBox m,
        ∃ (i : Fin (m + 1)) (U : Set (Work.Drive.Amb m)) (η : ℝ → Work.Drive.Amb m),
        IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧ (∀ t : ℝ, η t i = 0) ∧
        ∀ y ∈ U, (y ∈ Z ↔ y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i)))
    (V : Work.Drive.Amb m → Work.Drive.Amb m) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVs : HasCompactSupport V)
    (hVpar : ∀ x ∈ Z ∩ Submission.Drive.unitBox m,
        ∀ (i : Fin (m + 1)) (U : Set (Work.Drive.Amb m)) (η : ℝ → Work.Drive.Amb m),
        IsOpen U → x ∈ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η → (∀ t : ℝ, η t i = 0) →
        (∀ y ∈ U, (y ∈ Z ↔ y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i))) →
        ∃ c : ℝ, c ≠ 0 ∧ V x = c • (EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η (x i)) (1 : ℝ)))
    (hface : ∀ b ∈ Z ∩ Submission.Drive.unitBoxBdry m,
        ∃ i : Fin (m + 1), (b i = 0 ∨ b i = 1) ∧
          (∀ j : Fin (m + 1), j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧ V b i ≠ 0)
    (x : Work.Drive.Amb m) (hx : x ∈ Z ∩ Submission.Drive.unitBox m) (t : ℝ)
    (hbox : ∀ u ∈ Set.uIcc (0 : ℝ) t, Work.Drive.flowGen V hV hVs u x ∈ Submission.Drive.unitBox m) :
    Work.Drive.flowGen V hV hVs t x ∈ Z := by
  classical
  -- the argument for `t ≥ 0`, applicable to any field satisfying the same hypotheses
  have hpos : ∀ (V' : Amb m → Amb m) (hV' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V')
      (hVs' : HasCompactSupport V')
      (hVpar' : ∀ y ∈ Z ∩ Submission.Drive.unitBox m,
        ∀ (i : Fin (m + 1)) (U : Set (Amb m)) (η : ℝ → Amb m),
        IsOpen U → y ∈ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η → (∀ t : ℝ, η t i = 0) →
        (∀ w ∈ U, (w ∈ Z ↔ w = (w i) • EuclideanSpace.single i (1 : ℝ) + η (w i))) →
        ∃ c : ℝ, c ≠ 0 ∧
          V' y = c • (EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η (y i)) (1 : ℝ)))
      (hface' : ∀ b ∈ Z ∩ Submission.Drive.unitBoxBdry m,
        ∃ i : Fin (m + 1), (b i = 0 ∨ b i = 1) ∧
          (∀ j : Fin (m + 1), j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧ V' b i ≠ 0)
      (t' : ℝ) (ht0 : 0 ≤ t')
      (hbox' : ∀ u ∈ Set.Icc (0 : ℝ) t', flowGen V' hV' hVs' u x ∈ Submission.Drive.unitBox m),
      flowGen V' hV' hVs' t' x ∈ Z := by
    intro V' hV' hVs' hVpar' hface' t' ht0 hbox'
    obtain ⟨L, hL⟩ := exists_lipschitzWith_of_contDiff_hasCompactSupport hV' hVs'
    set γ : ℝ → Amb m := fun s => flowGen V' hV' hVs' s x with hγdef
    have hγ0 : γ 0 = x := flowGen_zero V' hV' hVs' x
    have hγ : ∀ s : ℝ, HasDerivAt γ (V' (γ s)) s := fun s => flowGen_deriv V' hV' hVs' x s
    have hγc : Continuous γ := continuous_iff_continuousAt.mpr fun s => (hγ s).continuousAt
    set S : Set ℝ := {s | s ∈ Set.Icc (0 : ℝ) t' ∧ ∀ v ∈ Set.Icc (0 : ℝ) s, γ v ∈ Z} with hS
    have hS0 : 0 ∈ S := by
      refine ⟨⟨le_rfl, ht0⟩, ?_⟩
      intro v hv
      rw [Set.mem_Icc] at hv
      have hv0 : v = 0 := le_antisymm hv.2 hv.1
      rw [hv0, hγ0]
      exact hx.1
    have hSne : S.Nonempty := ⟨0, hS0⟩
    have hSbdd : BddAbove S := ⟨t', fun s hs => hs.1.2⟩
    set T : ℝ := sSup S with hT
    have hTle : T ≤ t' := csSup_le hSne fun s hs => hs.1.2
    have hTge : 0 ≤ T := by
      rw [hT]
      exact le_csSup hSbdd hS0
    have hTmem : T ∈ S := by
      refine ⟨⟨hTge, hTle⟩, ?_⟩
      intro v hv
      rw [Set.mem_Icc] at hv
      rcases lt_or_eq_of_le hv.2 with hlt | heq
      · obtain ⟨s, hsS, hvs⟩ := (lt_csSup_iff hSbdd hSne).mp (by rw [← hT]; exact hlt)
        exact hsS.2 v ⟨hv.1, le_of_lt hvs⟩
      · rw [heq]
        rcases eq_or_lt_of_le hTge with h0 | h0
        · rw [← h0, hγ0]
          exact hx.1
        · have hcl : IsClosed (γ ⁻¹' Z) := hZ.preimage hγc
          have hsub : Set.Ico (0 : ℝ) T ⊆ γ ⁻¹' Z := by
            intro w hw
            rw [Set.mem_Ico] at hw
            obtain ⟨s, hsS, hws⟩ := (lt_csSup_iff hSbdd hSne).mp (by rw [← hT]; exact hw.2)
            exact hsS.2 w ⟨hw.1, le_of_lt hws⟩
          have hclo : T ∈ closure (Set.Ico (0 : ℝ) T) := by
            rw [closure_Ico (ne_of_lt h0)]
            exact ⟨hTge, le_rfl⟩
          exact hcl.closure_subset (closure_mono hsub hclo)
    -- if `T < t'`, the flow line would stay on `Z` a little beyond `T`
    have hTE : T = t' := by
      by_contra hne
      have hTlt : T < t' := lt_of_le_of_ne hTle hne
      have hqZ : γ T ∈ Z := hTmem.2 T ⟨hTge, le_rfl⟩
      have hqbox : γ T ∈ Submission.Drive.unitBox m := hbox' T ⟨hTge, le_of_lt hTlt⟩
      obtain ⟨i, U, η, hU, hqU, hηcd, hηi, hprop⟩ := hgra (γ T) ⟨hqZ, hqbox⟩
      obtain ⟨c, hc, hVeq⟩ := hVpar' (γ T) ⟨hqZ, hqbox⟩ i U η hU hqU hηcd hηi hprop
      have hbox_right : ∀ s ∈ Set.Ioc T t', γ s ∈ Submission.Drive.unitBox m :=
        fun s hs => hbox' s ⟨le_of_lt (lt_of_le_of_lt hTge hs.1), hs.2⟩
      obtain ⟨ρ, hρ, hρ'⟩ := graphMap_mem_of_side hU hηcd hηi hprop hqU hqZ hqbox hγ hface'
        hbox_right hTlt hVeq hc
      have htan : ∀ u : ℝ, |u - (γ T) i| < ρ → 0 ≤ (u - (γ T) i) * c →
          V' (ManifoldParity.graphMap i η u) =
            fderiv ℝ (ManifoldParity.graphMap i η) u
              ((V' (ManifoldParity.graphMap i η u)) i) :=
        fun u hu huc =>
          graphMap_tangency hU hηcd hηi hprop hVpar' (hρ' u hu huc).1
            (graphMap_mem_of_prop hηi hprop (hρ' u hu huc).1) (hρ' u hu huc).2
      have hZg : ∀ u : ℝ, |u - (γ T) i| < ρ → 0 ≤ (u - (γ T) i) * c →
          ManifoldParity.graphMap i η u ∈ Z :=
        fun u hu huc => graphMap_mem_of_prop hηi hprop (hρ' u hu huc).1
      -- the flow line, shifted to the starting time `T`
      set γ' : ℝ → Amb m := fun s => γ (s + T) with hγ'def
      have hγ' : ∀ s : ℝ, HasDerivAt γ' (V' (γ' s)) s := by
        intro s
        have h1 : HasDerivAt γ (V' (γ (s + T))) (s + T) := hγ (s + T)
        exact h1.comp_add_const s T
      have hγ'0 : γ' 0 = γ T := by simp [hγ'def]
      have hγ'c : Continuous γ' := continuous_iff_continuousAt.mpr fun s => (hγ' s).continuousAt
      have hVi : (V' (γ T)) i = c := by
        rw [hVeq]
        exact smul_par_apply_i ((hηcd.differentiable (by simp)).differentiableAt) hηi
      -- the flow line moves to the side of `γ T` selected by the sign of `c`
      have hmotion : ∃ ε₁ : ℝ, 0 < ε₁ ∧
          ∀ s ∈ Set.Icc (0 : ℝ) ε₁, 0 ≤ ((γ' s) i - (γ T) i) * c := by
        have hderiv : HasDerivAt (fun s : ℝ => (γ' s) i) c 0 := by
          have h1 := Work.Drive.hasDerivAt_apply (hγ' 0) i
          rw [hγ'0, hVi] at h1
          exact h1
        obtain ⟨ε₁, hε₁, hε₁'⟩ := exists_forall_mul_nonneg hderiv hc
        refine ⟨ε₁, hε₁, fun s hs => ?_⟩
        have h := hε₁' s hs
        rwa [hγ'0] at h
      obtain ⟨ε₁, hε₁, hε₁'⟩ := hmotion
      -- and it stays close to `γ T`
      obtain ⟨ε₂, hε₂, hε₂'⟩ : ∃ ε₂ : ℝ, 0 < ε₂ ∧
          ∀ s : ℝ, |s| < ε₂ → ‖γ' s - γ T‖ < ρ := by
        have hball : Metric.ball (γ' 0) ρ ∈ 𝓝 (γ' 0) := Metric.ball_mem_nhds _ hρ
        obtain ⟨ε₂, hε₂, hε₂'⟩ :=
          Metric.eventually_nhds_iff.mp (hγ'c.continuousAt.preimage_mem_nhds hball)
        refine ⟨ε₂, hε₂, fun s hs => ?_⟩
        have h := hε₂' (by rwa [Real.dist_eq, sub_zero])
        rwa [hγ'0] at h
      set e₃ : ℝ := min (min (ε₁ / 2) (ε₂ / 2)) ((t' - T) / 2) with he₃
      have he₃pos : 0 < e₃ := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
      have he₃le : e₃ ≤ min (ε₁ / 2) (ε₂ / 2) := min_le_left _ _
      have he₃le1 : e₃ ≤ ε₁ / 2 := le_trans he₃le (min_le_left _ _)
      have he₃le2 : e₃ ≤ ε₂ / 2 := le_trans he₃le (min_le_right _ _)
      have hstep : ∀ s ∈ Set.Icc (0 : ℝ) e₃,
          |(γ' s) i - (γ T) i| < ρ ∧ 0 ≤ ((γ' s) i - (γ T) i) * c := by
        intro s hs
        have hs1 : s ∈ Set.Icc (0 : ℝ) ε₁ :=
          ⟨hs.1, by linarith [hs.2, he₃le1]⟩
        have hs2 : |s| < ε₂ := by
          rw [abs_of_nonneg hs.1]
          linarith [hs.2, he₃le2]
        refine ⟨?_, hε₁' s hs1⟩
        have h1 : |(γ' s) i - (γ T) i| ≤ ‖γ' s - γ T‖ := by
          have h := PiLp.norm_apply_le (γ' s - γ T) i
          simpa [PiLp.sub_apply, Real.norm_eq_abs] using h
        exact lt_of_le_of_lt h1 (hε₂' s hs2)
      have hfinal : ∀ s ∈ Set.Icc (0 : ℝ) e₃, γ' s ∈ Z :=
        local_forward_mem_of_graph (q := γ T) (c := c) (ρ := ρ) (ε := e₃)
          hL hγ' hγ'0 hηcd (eq_graphMap_of_mem_prop hprop hqU hqZ).symm hc he₃pos hρ
          hstep htan hZg
      -- so `T` was not maximal
      have hmem : T + e₃ / 2 ∈ S := by
        have hle_t' : T + e₃ / 2 ≤ t' := by
          have h2 : e₃ ≤ (t' - T) / 2 := min_le_right _ _
          linarith
        refine ⟨⟨by linarith, hle_t'⟩, ?_⟩
        intro v hv
        rw [Set.mem_Icc] at hv
        rcases lt_or_ge T v with hlt | hle
        · have hv' : v - T ∈ Set.Icc (0 : ℝ) e₃ := by
            refine ⟨by linarith, ?_⟩
            have h2 : e₃ ≤ (t' - T) / 2 := min_le_right _ _
            linarith
          have h1 : γ ((v - T) + T) ∈ Z := hfinal (v - T) hv'
          have h2 : (v - T) + T = v := by ring
          rwa [h2] at h1
        · exact hTmem.2 v ⟨hv.1, hle⟩
      have hle := le_csSup hSbdd hmem
      rw [hT] at hle
      linarith
    have hlast : γ t' ∈ Z := by
      rw [← hTE]
      exact hTmem.2 T ⟨hTge, le_rfl⟩
    simpa [hγdef] using hlast
  by_cases ht : (0 : ℝ) ≤ t
  · refine hpos V hV hVs hVpar hface t ht ?_
    intro u hu
    exact hbox u (by rw [Set.uIcc_of_le ht]; exact hu)
  · -- `t < 0`: apply the nonnegative case to the reversed field `-V`
    have htneg : t < 0 := not_le.mp ht
    have hV1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (-V) := hV.neg
    have hVs1 : HasCompactSupport (-V) := hVs.neg
    have hVpar1 : ∀ y ∈ Z ∩ Submission.Drive.unitBox m,
        ∀ (i : Fin (m + 1)) (U : Set (Amb m)) (η : ℝ → Amb m),
        IsOpen U → y ∈ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η → (∀ t : ℝ, η t i = 0) →
        (∀ w ∈ U, (w ∈ Z ↔ w = (w i) • EuclideanSpace.single i (1 : ℝ) + η (w i))) →
        ∃ c : ℝ, c ≠ 0 ∧
          (-V) y = c • (EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η (y i)) (1 : ℝ)) := by
      intro y hy i U η hU hyU hηcd hηi hprop
      obtain ⟨c, hc, hceq⟩ := hVpar y hy i U η hU hyU hηcd hηi hprop
      exact ⟨-c, neg_ne_zero.mpr hc, by rw [Pi.neg_apply, hceq, neg_smul]⟩
    have hface1 : ∀ b ∈ Z ∩ Submission.Drive.unitBoxBdry m,
        ∃ i : Fin (m + 1), (b i = 0 ∨ b i = 1) ∧
          (∀ j : Fin (m + 1), j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧ (-V) b i ≠ 0 := by
      intro b hb
      obtain ⟨i, hi, hoth, hne⟩ := hface b hb
      exact ⟨i, hi, hoth, by simpa using hne⟩
    have hbox1 : ∀ u ∈ Set.Icc (0 : ℝ) (-t),
        flowGen (-V) hV1 hVs1 u x ∈ Submission.Drive.unitBox m := by
      intro u hu
      rw [flowGen_neg V hV hVs hV1 hVs1 u x]
      refine hbox (-u) ?_
      rw [Set.uIcc_comm, Set.uIcc_of_le htneg.le]
      exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have hfin := hpos (-V) hV1 hVs1 hVpar1 hface1 (-t) (by linarith) hbox1
    rw [flowGen_neg V hV hVs hV1 hVs1 (-t) x] at hfin
    simpa using hfin

end

end Work.Drive.ppIntrinsic
