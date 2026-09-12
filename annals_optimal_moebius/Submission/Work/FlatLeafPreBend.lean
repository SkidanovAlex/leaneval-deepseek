import Submission.Work.FlatComponents
import Submission.PaperBand.EmbeddingFacts

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Pre-bend property of flat-component seam chords (FlatLeafPreBend)

A straight chord `γ(s) = (1−s)A + sB` (`s ∈ [0,1]`) whose OPEN part
(`s ∈ (0,1)`) lies inside a flat component `C := flatComponent f p` is a
PRE-BEND of the embedded band: `‖f B − f A‖ = ‖B − A‖`.  This is the
flat-leaf counterpart of `BendImage.bend_length_eq` (the U-leaf pre-bend);
it is what makes the flat leaves of the Prop-main0 foliation satisfy the
`BandFoliation.preBend` field even though their endpoints sit on the seam
boundary (where `f` is only continuous, not known to be locally affine).

The proof:
* `segP_mem_unitStrip` — the whole closed segment stays in the closed
  unit strip (both endpoints there);
* `tendsto_segment_f_right` / `tendsto_segment_f_left` — `f` is
  continuous at the endpoints along the segment (1-Lipschitz bound
  `embedding_lipschitz`);
* `affineOn_segment_of_flat_open` — open-affineness plus one-sided
  endpoint continuity forces the affine formula to hold at the endpoints;
* `flat_open_segment_affine` — on the open part `f ∘ γ` is affine with
  the derivative of `f` at `x₀ := γ(1/2)` (by `flatComponent_affine`);
* **`seam_chord_preBend`** — `‖f B − f A‖ = ‖B − A‖` for a seam chord
  whose open part lies in a flat component (derivative isometry
  `fderiv_norm_eq_interior`).

Build: `lake build Submission.Work.FlatLeafPreBend` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- The affine segment map between two strip points. -/
def segP (A B : ℝ²) (s : ℝ) : ℝ² := (1 - s) • A + s • B

/-- Endpoint values of the segment map. -/
lemma segP_zero (A B : ℝ²) : segP A B 0 = A := by
  dsimp [segP]
  simp

lemma segP_one (A B : ℝ²) : segP A B 1 = B := by
  dsimp [segP]
  simp

/-- Difference of two points of the segment: `γ s − γ t = (s−t)•(B−A)`. -/
lemma segP_sub (A B : ℝ²) (s t : ℝ) :
    segP A B s - segP A B t = (s - t) • (B - A) := by
  dsimp [segP]
  ext i <;> simp <;> ring

/-- The whole closed segment between two unit-strip points stays in the
unit strip. -/
lemma segP_mem_unitStrip {A B : ℝ²} (hA : A ∈ unitStrip) (hB : B ∈ unitStrip)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) : segP A B s ∈ unitStrip := by
  have hA0 : A 0 ∈ Set.Icc (0 : ℝ) 1 := by simpa [unitStrip] using hA
  have hB0 : B 0 ∈ Set.Icc (0 : ℝ) 1 := by simpa [unitStrip] using hB
  rw [unitStrip]
  change (segP A B s) 0 ∈ Set.Icc (0 : ℝ) 1
  rw [Set.mem_Icc] at hs
  have hs0 : 0 ≤ s := hs.1
  have h1s : 0 ≤ 1 - s := by linarith
  have hc0 : (segP A B s) 0 = (1 - s) * (A 0) + s * (B 0) := by
    dsimp [segP]
  rw [hc0]
  constructor
  · have h1 : 0 ≤ (1 - s) * (A 0) := mul_nonneg h1s (Set.mem_Icc.mp hA0).1
    have h2 : 0 ≤ s * (B 0) := mul_nonneg hs0 (Set.mem_Icc.mp hB0).1
    linarith
  · have h1 : (1 - s) * (A 0) ≤ (1 - s) * 1 :=
      mul_le_mul_of_nonneg_left (Set.mem_Icc.mp hA0).2 h1s
    have h2 : s * (B 0) ≤ s * 1 := mul_le_mul_of_nonneg_left (Set.mem_Icc.mp hB0).2 hs0
    have hb : (1 - s) * 1 + s * 1 = 1 := by ring
    nlinarith

/-- `f` is continuous at the left endpoint of the segment from inside:
`f (γ s) → f (γ 0)` as `s → 0⁺`. -/
lemma tendsto_segment_f_right {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {A B : ℝ²} (hA : A ∈ unitStrip) (hB : B ∈ unitStrip) :
    Tendsto (fun s : ℝ => f (segP A B s)) (𝓝[>] (0 : ℝ)) (𝓝 (f (segP A B 0))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let K : ℝ := ‖B - A‖ + 1
  have hK : 0 < K := by dsimp [K]; linarith [norm_nonneg (B - A)]
  have hδpos : 0 < min 1 (ε / K) := lt_min (by norm_num) (div_pos hε hK)
  have hmem : Set.Ioo (0 : ℝ) (min 1 (ε / K)) ∈ 𝓝[>] (0 : ℝ) := by
    exact Ioo_mem_nhdsWithin_Ioi hδpos
  filter_upwards [hmem] with s hs
  rw [dist_eq_norm]
  have hs0 : 0 < s := hs.1
  have hsK : s < ε / K := lt_of_lt_of_le hs.2 (min_le_right 1 (ε / K))
  have hs1 : s ≤ 1 := le_of_lt (lt_of_lt_of_le hs.2 (min_le_left 1 (ε / K)))
  have hγ : segP A B s ∈ unitStrip := segP_mem_unitStrip hA hB ⟨le_of_lt hs0, hs1⟩
  have hγ0 : segP A B 0 ∈ unitStrip := by rw [segP_zero]; exact hA
  have hlip : ‖f (segP A B s) - f (segP A B 0)‖ ≤ ‖segP A B s - segP A B 0‖ :=
    embedding_lipschitz hf (x := segP A B 0) hγ0 (y := segP A B s) hγ
  have hΔ : segP A B s - segP A B 0 = s • (B - A) := by
    simpa using segP_sub A B s 0
  have habs : |s| = s := abs_of_pos hs0
  have hb : s * ‖B - A‖ < ε := by
    have hle : s * ‖B - A‖ ≤ s * K :=
      mul_le_mul_of_nonneg_left (by dsimp [K]; linarith) (le_of_lt hs0)
    have hsK' : s * K < ε := by
      have hm := mul_lt_mul_of_pos_right hsK hK
      rwa [div_mul_cancel₀ ε (ne_of_gt hK)] at hm
    linarith
  calc
    ‖f (segP A B s) - f (segP A B 0)‖ ≤ ‖segP A B s - segP A B 0‖ := hlip
    _ = ‖s • (B - A)‖ := by rw [hΔ]
    _ = |s| * ‖B - A‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ = s * ‖B - A‖ := by rw [habs]
    _ < ε := hb

/-- `f` is continuous at the right endpoint of the segment from inside:
`f (γ s) → f (γ 1)` as `s → 1⁻`. -/
lemma tendsto_segment_f_left {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {A B : ℝ²} (hA : A ∈ unitStrip) (hB : B ∈ unitStrip) :
    Tendsto (fun s : ℝ => f (segP A B s)) (𝓝[<] (1 : ℝ)) (𝓝 (f (segP A B 1))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let K : ℝ := ‖B - A‖ + 1
  have hK : 0 < K := by dsimp [K]; linarith [norm_nonneg (B - A)]
  have hδpos : 0 < min 1 (ε / K) := lt_min (by norm_num) (div_pos hε hK)
  have hδle : min 1 (ε / K) ≤ 1 := min_le_left 1 (ε / K)
  have hlo : 1 - min 1 (ε / K) < 1 := by linarith
  have hmem : Set.Ioo (1 - min 1 (ε / K)) 1 ∈ 𝓝[<] (1 : ℝ) := by
    exact Ioo_mem_nhdsWithin_Iio hlo
  filter_upwards [hmem] with s hs
  rw [dist_eq_norm]
  have hs0 : 0 < s := by
    have : 0 ≤ 1 - min 1 (ε / K) := sub_nonneg.mpr hδle
    linarith [hs.1]
  have hs1 : s < 1 := hs.2
  have hδs : 1 - s < min 1 (ε / K) := by linarith [hs.1]
  have hγ : segP A B s ∈ unitStrip := segP_mem_unitStrip hA hB ⟨le_of_lt hs0, le_of_lt hs1⟩
  have hγ1 : segP A B 1 ∈ unitStrip := by rw [segP_one]; exact hB
  have hlip : ‖f (segP A B s) - f (segP A B 1)‖ ≤ ‖segP A B s - segP A B 1‖ :=
    embedding_lipschitz hf (x := segP A B 1) hγ1 (y := segP A B s) hγ
  have hΔ : segP A B s - segP A B 1 = (s - 1) • (B - A) := by
    simpa using segP_sub A B s 1
  have habs : |s - 1| = 1 - s := by
    rw [abs_of_neg (sub_neg.mpr hs1)]
    ring
  have hb : (1 - s) * ‖B - A‖ < ε := by
    have hle : (1 - s) * ‖B - A‖ ≤ (1 - s) * K :=
      mul_le_mul_of_nonneg_left (by dsimp [K]; linarith) (by linarith)
    have hsub : (1 - s) * K < ε := by
      have h1 : (1 - s) * K < min 1 (ε / K) * K :=
        mul_lt_mul_of_pos_right hδs hK
      have h2 : min 1 (ε / K) * K ≤ ε := by
        have hmin : min 1 (ε / K) ≤ ε / K := min_le_right 1 (ε / K)
        have h2' := mul_le_mul_of_nonneg_right hmin (le_of_lt hK)
        rwa [div_mul_cancel₀ ε (ne_of_gt hK)] at h2'
      linarith
    exact lt_of_le_of_lt hle hsub
  calc
    ‖f (segP A B s) - f (segP A B 1)‖ ≤ ‖segP A B s - segP A B 1‖ := hlip
    _ = ‖(s - 1) • (B - A)‖ := by rw [hΔ]
    _ = |s - 1| * ‖B - A‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ = (1 - s) * ‖B - A‖ := by rw [habs]
    _ < ε := hb

/-- Abstract endpoint-affine extension: if `G` is affine on the open
interval and continuous at the endpoints from inside, the affine formula
holds at the endpoints too. -/
lemma affineOn_segment_of_flat_open (G : ℝ → ℝ³) (x₀ c : ℝ³)
    (hG : ∀ s ∈ Set.Ioo (0 : ℝ) 1, G s = x₀ + (s - 1 / 2) • c)
    (h0 : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 (G 0)))
    (h1 : Tendsto G (𝓝[<] (1 : ℝ)) (𝓝 (G 1))) :
    G 0 = x₀ + ((0 : ℝ) - 1 / 2) • c ∧ G 1 = x₀ + ((1 : ℝ) - 1 / 2) • c := by
  let L : ℝ → ℝ³ := fun s => x₀ + (s - 1 / 2) • c
  have hcontL : Continuous L := by
    unfold L
    fun_prop
  -- agreement on (0,1), which is a punctured right-nbhd of 0 and
  -- punctured left-nbhd of 1
  have hIoo0 : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsWithin_Ioi (by norm_num : (0 : ℝ) < 1)
  have hIoo1 : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) :=
    Ioo_mem_nhdsWithin_Iio (by norm_num : (0 : ℝ) < 1)
  have hEq0 : G =ᶠ[𝓝[>] (0 : ℝ)] L := by
    rw [Filter.EventuallyEq]
    refine eventually_of_mem hIoo0 ?_
    intro s hs
    dsimp [L]
    exact hG s hs
  have hEq1 : G =ᶠ[𝓝[<] (1 : ℝ)] L := by
    rw [Filter.EventuallyEq]
    refine eventually_of_mem hIoo1 ?_
    intro s hs
    dsimp [L]
    exact hG s hs
  have hgt0 : Tendsto L (𝓝[>] (0 : ℝ)) (𝓝 (L 0)) :=
    (hcontL.tendsto 0).mono_left (by unfold nhdsWithin; exact inf_le_left)
  have hgt1 : Tendsto L (𝓝[<] (1 : ℝ)) (𝓝 (L 1)) :=
    (hcontL.tendsto 1).mono_left (by unfold nhdsWithin; exact inf_le_left)
  have hφt0 : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 (L 0)) := hgt0.congr' hEq0.symm
  have hφt1 : Tendsto G (𝓝[<] (1 : ℝ)) (𝓝 (L 1)) := hgt1.congr' hEq1.symm
  have hEqv0 : G 0 = L 0 := tendsto_nhds_unique h0 hφt0
  have hEqv1 : G 1 = L 1 := tendsto_nhds_unique h1 hφt1
  constructor
  · dsimp [L] at hEqv0
    exact hEqv0
  · dsimp [L] at hEqv1
    exact hEqv1

/-- Open-part affineness of the image of a flat segment: with
`x₀ = γ(1/2)`, `c = fderiv f x₀ (B−A)`, `f (γ s) = f x₀ + (s−1/2)•c` on
the open segment. -/
lemma flat_open_segment_affine {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p A B : ℝ²} (hopen : ∀ s ∈ Set.Ioo (0 : ℝ) 1, segP A B s ∈ flatComponent f p) :
    ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      f (segP A B s) =
        f (segP A B (1 / 2)) + (s - 1 / 2) • (fderiv ℝ f (segP A B (1 / 2)) (B - A)) := by
  intro s hs
  let x₀ : ℝ² := segP A B (1 / 2)
  let c : ℝ³ := fderiv ℝ f x₀ (B - A)
  have hx₀ : x₀ ∈ flatComponent f p := by
    dsimp [x₀]
    exact hopen (1 / 2) ⟨by norm_num, by norm_num⟩
  have hz : segP A B s ∈ flatComponent f p := hopen s hs
  have haff := flatComponent_affine hf hx₀ (segP A B s) hz
  have hΔ : segP A B s - x₀ = (s - 1 / 2) • (B - A) := by
    dsimp [x₀]
    exact segP_sub A B s (1 / 2)
  rw [hΔ] at haff
  have hlin : (fderiv ℝ f x₀) ((s - 1 / 2) • (B - A)) = (s - 1 / 2) • c := by
    dsimp [c]
    rw [ContinuousLinearMap.map_smul]
  rwa [hlin] at haff

/-- **A chord whose open part lies in a flat component is a pre-bend**:
`‖f B − f A‖ = ‖B − A‖`. -/
theorem seam_chord_preBend {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p A B : ℝ²}
    (hA : A ∈ unitStrip) (hB : B ∈ unitStrip)
    (hopen : ∀ s ∈ Set.Ioo (0 : ℝ) 1, segP A B s ∈ flatComponent f p) :
    ‖f B - f A‖ = ‖B - A‖ := by
  let x₀ : ℝ² := segP A B (1 / 2)
  let c : ℝ³ := fderiv ℝ f x₀ (B - A)
  have hx₀ : x₀ ∈ flatComponent f p := by
    dsimp [x₀]
    exact hopen (1 / 2) ⟨by norm_num, by norm_num⟩
  have hx₀S : x₀ ∈ stripInterior := flatComponent_subset_stripInterior f p hx₀
  have hG : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      f (segP A B s) = f x₀ + (s - 1 / 2) • c := by
    intro s hs
    have hh := flat_open_segment_affine hf (p := p) (A := A) (B := B) hopen s hs
    dsimp [x₀, c] at hh ⊢
    exact hh
  have hend := affineOn_segment_of_flat_open (fun s : ℝ => f (segP A B s)) (f x₀) c hG
    (tendsto_segment_f_right hf hA hB) (tendsto_segment_f_left hf hA hB)
  have hAval : f A = f x₀ + ((0 : ℝ) - 1 / 2) • c := by
    have hh := hend.1
    rw [segP_zero] at hh
    exact hh
  have hBval : f B = f x₀ + ((1 : ℝ) - 1 / 2) • c := by
    have hh := hend.2
    rw [segP_one] at hh
    exact hh
  have hdiff : f B - f A = c := by
    rw [hBval, hAval]
    calc
      (f x₀ + ((1 : ℝ) - 1 / 2) • c) - (f x₀ + ((0 : ℝ) - 1 / 2) • c)
          = ((1 : ℝ) - 1 / 2) • c - ((0 : ℝ) - 1 / 2) • c := by abel
      _ = (((1 : ℝ) - 1 / 2) - ((0 : ℝ) - 1 / 2)) • c := by rw [← sub_smul]
      _ = c := by
        have hsc : ((1 : ℝ) - 1 / 2) - ((0 : ℝ) - 1 / 2) = 1 := by norm_num
        rw [hsc, one_smul]
  have hnormc : ‖c‖ = ‖B - A‖ := by
    dsimp [c]
    exact fderiv_norm_eq_interior hf x₀ hx₀S (B - A)
  rw [hdiff, hnormc]

end Submission.PaperBand
