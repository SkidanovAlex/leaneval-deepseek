import Mathlib
import Submission.Work.Drive.ppIntrinsic.FlowGen
import Submission.Work.Drive.ManifoldParity.FlowSetupDefs
import Submission.Work.Drive.ManifoldParity.FlowSetupPairing
import Submission.Work.Drive.finite_of_isCompact_of_isolated
import Submission.Work.Drive.crossing_of_deriv_ne_zero

/-!
# The intrinsic boundary parity of a compact locally-graph set

`K ⊆ ℝ^{m+1}` is compact, `Z` closed with `K ⊆ Z`, and `Z` is locally a graph over a coordinate axis
(`hgra`), with a smooth compactly supported field `V` which is tangent to `Z` at every point of `K`
(`hVpar`), non-zero there (`hVne`), crosses the faces of the box (`hface`) and whose flow preserves
`K` while it stays in the box (`hmapsTo`).

The conclusion is that `K ∩ ∂[0,1]^{m+1}` is **finite** and has **even** cardinality.

* finiteness: every boundary point `b` is isolated in `K ∩ ∂` — the chart of `hgra` at `b` presents
  `Z` near `b` as a curve `u ↦ u • eᵢ + η u`, and `hface` together with `hVpar` makes the curve cross
  the face of the box transversally at `b` (`Work.Drive.crossing_of_deriv_ne_zero_gen`);
* evenness: `Work.Drive.even_ncard_boundary` applied to the flow setup of `flowGen V` on `K`, with a
  finite cover by `FlowChart`s built from the local graph data.
-/

namespace Work.Drive.ppIntrinsic

open scoped ContDiff Topology
open Set

noncomputable section

/-- The flow setup of the global flow of a compactly supported smooth field `V` acting on a set `K`
which is invariant under it while the flow line stays in the unit box. -/
def driveSetup {m : ℕ} (V : Amb m → Amb m) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVs : HasCompactSupport V) (K : Set (Amb m))
    (hmapsTo : ∀ x ∈ K, ∀ t : ℝ,
      (∀ u ∈ Set.uIcc (0 : ℝ) t, flowGen V hV hVs u x ∈ Submission.Drive.unitBox m) →
      flowGen V hV hVs t x ∈ K) : FlowSetup m where
  W := V
  Φ := flowGen V hV hVs
  K := K
  zero := fun x => flowGen_zero V hV hVs x
  add := fun s t x => flowGen_add V hV hVs s t x
  deriv := fun x t => flowGen_deriv V hV hVs x t
  mapsTo := hmapsTo
  cont := hV.continuous

/-- **The local chart of `K` at a point of `K`.**  From the local graph presentation of `Z` and the
tangentiality of `V` one gets a `FlowChart` for `K` at `x`: `K` is the graph of `η` near `x` and the
`i`-th component of `V` is bounded below by `|V x i| / 2` there. -/
theorem flowChart_at_of_localGraph {m : ℕ} {Z K : Set (Amb m)} (hKZ : K ⊆ Z)
    (hgra : ∀ x ∈ K, ∃ (i : Fin (m + 1)) (U : Set (Amb m)) (η : ℝ → Amb m),
        IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧ (∀ t : ℝ, η t i = 0) ∧
        ∀ y ∈ U, (y ∈ Z ↔ y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i)))
    (V : Amb m → Amb m) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVpar : ∀ x ∈ K, ∀ (i : Fin (m + 1)) (U : Set (Amb m)) (η : ℝ → Amb m),
        IsOpen U → x ∈ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η → (∀ t : ℝ, η t i = 0) →
        (∀ y ∈ U, (y ∈ Z ↔ y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i))) →
        ∃ c : ℝ, c ≠ 0 ∧ V x = c • (EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η (x i)) (1 : ℝ)))
    {x : Amb m} (hx : x ∈ K) : ∃ C : FlowChart V K x, x ∈ C.region := by
  obtain ⟨i, U, η, hUopen, hxU, hηcd, hηi, hchart⟩ := hgra x hx
  obtain ⟨c, hcne, hVc⟩ := hVpar x hx i U η hUopen hxU hηcd hηi hchart
  -- the derivative of `η` and the vanishing of its `i`-th component
  have hderiv : HasDerivAt η ((fderiv ℝ η (x i)) (1 : ℝ)) (x i) :=
    (hηcd.differentiable (by simp) (x i)).hasFDerivAt.hasDerivAt
  have hderiv_i : ((fderiv ℝ η (x i)) (1 : ℝ)) i = 0 := by
    have h1 : HasDerivAt (fun u : ℝ => η u i) (((fderiv ℝ η (x i)) (1 : ℝ)) i) (x i) :=
      hasDerivAt_apply hderiv i
    have h2 : HasDerivAt (fun u : ℝ => η u i) 0 (x i) := by
      have hfun : (fun u : ℝ => η u i) = fun _ => (0 : ℝ) := funext fun u => hηi u
      rw [hfun]; exact hasDerivAt_const (x i) 0
    exact h1.unique h2
  have hVxi : V x i = c := by
    have h := congrArg (fun z : Amb m => z i) hVc
    simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul] at h
    rw [hderiv_i] at h
    simpa using h
  have hVi_ne : V x i ≠ 0 := by rw [hVxi]; exact hcne
  have hVi_pos : 0 < |V x i| := abs_pos.mpr hVi_ne
  -- the three radius choices
  have hcont_i : Continuous fun y : Amb m => V y i :=
    (PiLp.continuous_apply 2 (fun _ : Fin (m + 1) => ℝ) i).comp hV.continuous
  obtain ⟨εV, hεV, hεV'⟩ : ∃ εV > 0, ∀ y, ‖y - x‖ < εV → |V y i - V x i| < |V x i| / 2 := by
    have hhalf : 0 < |V x i| / 2 := by linarith
    obtain ⟨εV, hεV, h⟩ := Metric.continuousAt_iff.mp hcont_i.continuousAt (|V x i| / 2) hhalf
    exact ⟨εV, hεV, fun y hy => by
      have h' := h (by rwa [dist_eq_norm])
      rwa [Real.dist_eq] at h'⟩
  obtain ⟨εU, hεU, hεU'⟩ : ∃ εU > 0, ∀ y, ‖y - x‖ < εU → y ∈ U := by
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hUopen x hxU
    exact ⟨r, hr, fun y hy => hrU (by rw [Metric.mem_ball, dist_eq_norm]; exact hy)⟩
  set R : ℝ := min εV εU with hRdef
  have hRpos : 0 < R := by rw [hRdef]; exact lt_min hεV hεU
  have hRV : R ≤ εV := by rw [hRdef]; exact min_le_left _ _
  have hRU : R ≤ εU := by rw [hRdef]; exact min_le_right _ _
  have hR3 : 0 < R / 3 := by linarith
  obtain ⟨εη, hεη, hεη'⟩ : ∃ εη > 0, ∀ u, |u - x i| < εη → ‖η u - η (x i)‖ < R / 3 := by
    obtain ⟨εη, hεη, h⟩ := Metric.continuousAt_iff.mp hηcd.continuous.continuousAt (R / 3) hR3
    exact ⟨εη, hεη, fun u hu => by
      have h' := h (by rwa [Real.dist_eq])
      rwa [dist_eq_norm] at h'⟩
  have hηx : η (x i) = x - (x i) • EuclideanSpace.single i (1 : ℝ) := by
    rw [eq_sub_iff_add_eq]
    rw [show η (x i) + (x i) • EuclideanSpace.single i (1 : ℝ) =
        (x i) • EuclideanSpace.single i (1 : ℝ) + η (x i) from by abel]
    exact ((hchart x hxU).mp (hKZ hx)).symm
  set δs : ℝ := min εη (R / 3) with hδsdef
  set cval : ℝ := |V x i| / 2 with hcvaldef
  have hδs : 0 < δs := by rw [hδsdef]; exact lt_min hεη hR3
  have hcval : 0 < cval := by rw [hcvaldef]; linarith
  have hδs3 : δs ≤ R / 3 := by rw [hδsdef]; exact min_le_right _ _
  have hδsη : δs ≤ εη := by rw [hδsdef]; exact min_le_left _ _
  have hball : ∀ y : Amb m, |y i - x i| < δs →
      ‖y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)‖ < R / 3 → ‖y - x‖ < R := by
    intro y h1 h2
    have h1' : |y i - x i| < R / 3 := lt_of_lt_of_le h1 hδs3
    have h1'' : |y i - x i| < εη := lt_of_lt_of_le h1 hδsη
    have h3 : ‖η (y i) - η (x i)‖ < R / 3 := hεη' (y i) h1''
    have hdecomp : y - x = (y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)) +
        (η (y i) - η (x i)) + ((y i - x i) • EuclideanSpace.single i (1 : ℝ)) := by
      rw [hηx]; module
    have hsingle : ‖(y i - x i) • EuclideanSpace.single (i : Fin (m + 1)) (1 : ℝ)‖ = |y i - x i| := by
      rw [norm_smul, Real.norm_eq_abs, PiLp.norm_single]
      simp
    rw [hdecomp]
    calc ‖(y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)) + (η (y i) - η (x i)) +
          ((y i - x i) • EuclideanSpace.single i (1 : ℝ))‖
        ≤ ‖y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)‖ + ‖η (y i) - η (x i)‖ +
          ‖(y i - x i) • EuclideanSpace.single i (1 : ℝ)‖ := by
          have h1 := norm_add_le (y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i))
            (η (y i) - η (x i))
          have h2 := norm_add_le
            ((y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)) + (η (y i) - η (x i)))
            ((y i - x i) • EuclideanSpace.single i (1 : ℝ))
          linarith
      _ = ‖y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)‖ + ‖η (y i) - η (x i)‖ +
          |y i - x i| := by rw [hsingle]
      _ < R := by linarith
  have hgraphs : ∀ y : Amb m, |y i - x i| < δs →
      ‖y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)‖ < R / 3 → y ∈ K →
      y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i) := by
    intro y h1 h2 hy
    have hb := hball y h1 h2
    have hyU : y ∈ U := hεU' y (lt_of_lt_of_le hb hRU)
    exact (hchart y hyU).mp (hKZ hy)
  have hvels : ∀ y : Amb m, |y i - x i| < δs →
      ‖y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)‖ < R / 3 → cval ≤ |V y i| := by
    intro y h1 h2
    have hb := hball y h1 h2
    have hεV'' : ‖y - x‖ < εV := lt_of_lt_of_le hb hRV
    have hlt : |V y i - V x i| < |V x i| / 2 := hεV' y hεV''
    have htri : |V x i| - |V y i| ≤ |V x i - V y i| := by
      have h := abs_add_le (V x i - V y i) (V y i)
      rw [sub_add_cancel] at h
      linarith
    have hlt' : |V x i - V y i| < |V x i| / 2 := by rwa [abs_sub_comm] at hlt
    have hlt'' : |V x i| - |V y i| < |V x i| / 2 := lt_of_le_of_lt htri hlt'
    rw [hcvaldef]
    linarith
  let C : FlowChart V K x :=
    { i := i, δ := δs, ρ := R / 3, c := cval, η := η, hδ := hδs, hρ := hR3,
      hc := hcval, hηc := hηcd.continuous, hηi := hηi, hgraph := hgraphs, hvel := hvels }
  refine ⟨C, ?_⟩
  rw [FlowChart.mem_region]
  refine ⟨by simp only [sub_self, abs_zero]; exact hδs, ?_⟩
  have h0 : x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i) = 0 := by rw [hηx]; abel
  rw [h0, norm_zero]
  exact hR3

/-- **A finite chart cover of `K ∩ [0,1]^{m+1}`.** -/
theorem exists_flowCover_of_localGraph {m : ℕ} {Z K : Set (Amb m)} (hK : IsCompact K)
    (hKZ : K ⊆ Z)
    (hgra : ∀ x ∈ K, ∃ (i : Fin (m + 1)) (U : Set (Amb m)) (η : ℝ → Amb m),
        IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧ (∀ t : ℝ, η t i = 0) ∧
        ∀ y ∈ U, (y ∈ Z ↔ y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i)))
    (V : Amb m → Amb m) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVs : HasCompactSupport V)
    (hVpar : ∀ x ∈ K, ∀ (i : Fin (m + 1)) (U : Set (Amb m)) (η : ℝ → Amb m),
        IsOpen U → x ∈ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η → (∀ t : ℝ, η t i = 0) →
        (∀ y ∈ U, (y ∈ Z ↔ y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i))) →
        ∃ c : ℝ, c ≠ 0 ∧ V x = c • (EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η (x i)) (1 : ℝ)))
    (hmapsTo : ∀ x ∈ K, ∀ t : ℝ,
      (∀ u ∈ Set.uIcc (0 : ℝ) t, flowGen V hV hVs u x ∈ Submission.Drive.unitBox m) →
      flowGen V hV hVs t x ∈ K) :
    Nonempty (FlowCover (driveSetup V hV hVs K hmapsTo)) := by
  classical
  have hpoint : ∀ x ∈ K, ∃ C : FlowChart V K x, x ∈ C.region :=
    fun x hx => flowChart_at_of_localGraph hKZ hgra V hV hVpar hx
  let Cof : ∀ x : Amb m, x ∈ K → FlowChart V K x := fun x hx => Classical.choose (hpoint x hx)
  have hKc : IsCompact (K ∩ Submission.Drive.unitBox m) :=
    hK.inter_right (isClosed_unitBox m)
  by_cases hne : (K ∩ Submission.Drive.unitBox m).Nonempty
  · haveI : Nonempty {x : Amb m // x ∈ K ∩ Submission.Drive.unitBox m} :=
      ⟨⟨hne.choose, hne.choose_spec⟩⟩
    obtain ⟨t, ht⟩ := hKc.elim_finite_subcover
      (fun x : {x : Amb m // x ∈ K ∩ Submission.Drive.unitBox m} => (Cof x.1 x.2.1).region)
      (fun x => (Cof x.1 x.2.1).isOpen_region)
      (fun x hx => Set.mem_iUnion.mpr
        ⟨⟨x, hx⟩, Classical.choose_spec (hpoint x hx.1)⟩)
    have hcover : K ∩ Submission.Drive.unitBox m ⊆
        ⋃ j : {j : {x : Amb m // x ∈ K ∩ Submission.Drive.unitBox m} // j ∈ t},
          (Cof j.1.1 j.1.2.1).region := by
      intro y hy
      have h := ht hy
      simp only [Set.mem_iUnion] at h
      obtain ⟨i, hi, hyi⟩ := h
      exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hyi⟩
    exact ⟨{ ι := {j : {x : Amb m // x ∈ K ∩ Submission.Drive.unitBox m} // j ∈ t},
             str := inferInstance, p := fun j => j.1.1, C := fun j => Cof j.1.1 j.1.2.1,
             cover := hcover }⟩
  · refine ⟨{ ι := Fin 0, str := inferInstance, p := fun j => j.elim0,
               C := fun j => j.elim0, cover := ?cvr }⟩
    intro y hy
    exact absurd ⟨y, hy⟩ hne

/-- **Isolation of a boundary point of `K`.**  Under the local graph presentation of `Z` at `b` and
the face data at `b`, every point of `K ∩ ∂[0,1]^{m+1}` close enough to `b` equals `b`. -/
theorem isolated_of_localGraph {m : ℕ} {Z K : Set (Amb m)} (hKZ : K ⊆ Z)
    (hgra : ∀ x ∈ K, ∃ (i : Fin (m + 1)) (U : Set (Amb m)) (η : ℝ → Amb m),
        IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧ (∀ t : ℝ, η t i = 0) ∧
        ∀ y ∈ U, (y ∈ Z ↔ y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i)))
    (V : Amb m → Amb m)
    (hVpar : ∀ x ∈ K, ∀ (i : Fin (m + 1)) (U : Set (Amb m)) (η : ℝ → Amb m),
        IsOpen U → x ∈ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η → (∀ t : ℝ, η t i = 0) →
        (∀ y ∈ U, (y ∈ Z ↔ y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i))) →
        ∃ c : ℝ, c ≠ 0 ∧ V x = c • (EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η (x i)) (1 : ℝ)))
    (hface : ∀ b ∈ K ∩ Submission.Drive.unitBoxBdry m,
        ∃ i : Fin (m + 1), (b i = 0 ∨ b i = 1) ∧
          (∀ j : Fin (m + 1), j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧ V b i ≠ 0)
    {b : Amb m} (hbK : b ∈ K) (hbB : b ∈ Submission.Drive.unitBoxBdry m) :
    ∃ U : Set (Amb m), IsOpen U ∧ b ∈ U ∧
      U ∩ (K ∩ Submission.Drive.unitBoxBdry m) ⊆ {b} := by
  obtain ⟨i, U₀, η, hUopen, hbU, hηcd, hηi, hchart⟩ := hgra b hbK
  obtain ⟨j, hbj, hbjother, hbjV⟩ := hface b ⟨hbK, hbB⟩
  obtain ⟨c, hcne, hVc⟩ := hVpar b hbK i U₀ η hUopen hbU hηcd hηi hchart
  set w : Amb m := EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η (b i)) (1 : ℝ) with hwdef
  -- the `j`-th component of `w` does not vanish, since `V b = c • w` and `V b j ≠ 0`
  have hwj : w j ≠ 0 := by
    intro h0
    have hVj : V b j = 0 := by
      rw [hVc]
      simp only [PiLp.smul_apply, h0, smul_eq_mul, mul_zero]
    exact hbjV hVj
  -- the curve `u ↦ u • eᵢ + η u` through `b`
  have hγderiv : HasDerivAt (fun u : ℝ => u • EuclideanSpace.single i (1 : ℝ) + η u) w (b i) := by
    have hη' : HasDerivAt η ((fderiv ℝ η (b i)) (1 : ℝ)) (b i) :=
      (hηcd.differentiable (by simp) (b i)).hasFDerivAt.hasDerivAt
    have h1 : HasDerivAt (fun u : ℝ => u • EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single i (1 : ℝ)) (b i) := by
      simpa using (hasDerivAt_id (b i)).smul_const (EuclideanSpace.single i (1 : ℝ))
    have h2 : HasDerivAt (fun u : ℝ => u • EuclideanSpace.single i (1 : ℝ) + η u)
        (EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η (b i)) (1 : ℝ)) (b i) :=
      h1.add hη'
    simpa [hwdef] using h2
  have hγcont : Continuous (fun u : ℝ => u • EuclideanSpace.single i (1 : ℝ) + η u) := by
    have h : Continuous fun u : ℝ => u • (EuclideanSpace.single i (1 : ℝ) : Amb m) :=
      continuous_id.smul continuous_const
    exact h.add hηcd.continuous
  have hγb : (fun u : ℝ => u • EuclideanSpace.single i (1 : ℝ) + η u) (b i) = b :=
    ((hchart b hbU).mp (hKZ hbK)).symm
  -- the shifted curve crosses the box boundary transversally at `b`
  set γ : ℝ → Amb m := fun s => (s + b i) • EuclideanSpace.single i (1 : ℝ) + η (s + b i) with hγdef
  have hγderiv' : HasDerivAt γ w 0 := by
    have h2 : HasDerivAt (fun u : ℝ => u • EuclideanSpace.single i (1 : ℝ) + η u) w (0 + b i) := by
      simpa using hγderiv
    have h3 := h2.comp_add_const 0 (b i)
    simpa [hγdef] using h3
  have hγcont' : Continuous γ := by
    rw [hγdef]
    have h : Continuous fun u : ℝ => u • (EuclideanSpace.single i (1 : ℝ) : Amb m) :=
      continuous_id.smul continuous_const
    have hcomp : Continuous fun s : ℝ => (s + b i) • (EuclideanSpace.single i (1 : ℝ) : Amb m) :=
      h.comp (continuous_id.add continuous_const)
    have hηcomp : Continuous fun s : ℝ => η (s + b i) :=
      hηcd.continuous.comp (continuous_id.add continuous_const)
    exact hcomp.add hηcomp
  have hγ0 : γ 0 = b := by
    rw [hγdef]
    simpa using hγb
  obtain ⟨ε, hε, hcase⟩ :=
    crossing_of_deriv_ne_zero_gen hγderiv' hγcont' hγ0 j ⟨hbj, hbjother⟩ hwj
  -- the isolating neighbourhood
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hUopen b hbU
  refine ⟨Metric.ball b (min r ε), Metric.isOpen_ball, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_self]
    exact lt_min hr hε
  · rintro y ⟨hyball, hyb⟩
    rw [Set.mem_singleton_iff]
    have hyK : y ∈ K := hyb.1
    have hyB : y ∈ Submission.Drive.unitBoxBdry m := hyb.2
    have hydist : ‖y - b‖ < min r ε := by
      rwa [Metric.mem_ball, dist_eq_norm] at hyball
    have hyU : y ∈ U₀ := by
      refine hrU ?_
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_lt_of_le hydist (min_le_left _ _)
    have hgraphy : y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i) :=
      (hchart y hyU).mp (hKZ hyK)
    have hyt : y = γ (y i - b i) := by
      rw [hγdef]
      simp only
      rw [show y i - b i + b i = y i by ring]
      exact hgraphy
    have hdi : |y i - b i| < ε := by
      have hcoord : (y - b) i = y i - b i := by simp
      have hle : |y i - b i| = ‖(y - b) i‖ := by rw [hcoord]; simp
      rw [hle]
      exact lt_of_le_of_lt (PiLp.norm_apply_le (y - b) i)
        (lt_of_lt_of_le hydist (min_le_right _ _))
    have hzi : y i - b i = 0 := by
      by_contra hne
      have ht : y i - b i ∈ Set.Ioo (-ε) ε := (abs_lt.mp hdi)
      have hmem : γ (y i - b i) ∈ Submission.Drive.unitBoxBdry m := by rw [← hyt]; exact hyB
      have hbox : γ (y i - b i) ∈ Submission.Drive.unitBox m := hmem.1
      have hnint : γ (y i - b i) ∉ interior (Submission.Drive.unitBox m) :=
        not_mem_interior_unitBox_of_mem_unitBoxBdry hmem
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact (h2 (y i - b i) ⟨by linarith [ht.1], hlt⟩) hbox
        · exact hnint (h1 (y i - b i) ⟨hlt, by linarith [ht.2]⟩)
      · rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact hnint (h1 (y i - b i) ⟨by linarith [ht.1], hlt⟩)
        · exact (h2 (y i - b i) ⟨hlt, by linarith [ht.2]⟩) hbox
    rw [hyt, hzi, hγdef]
    simpa using hγb

/-- **The boundary parity of a compact locally-graph set.** -/
theorem finite_and_even_ncard_bdry_of_localGraph {m : ℕ} {Z K : Set (Work.Drive.Amb m)}
    (hK : IsCompact K) (hZ : IsClosed Z) (hKZ : K ⊆ Z)
    (hgra : ∀ x ∈ K, ∃ (i : Fin (m + 1)) (U : Set (Work.Drive.Amb m)) (η : ℝ → Work.Drive.Amb m),
        IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧ (∀ t : ℝ, η t i = 0) ∧
        ∀ y ∈ U, (y ∈ Z ↔ y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i)))
    (V : Work.Drive.Amb m → Work.Drive.Amb m) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVs : HasCompactSupport V) (hVne : ∀ x ∈ K, V x ≠ 0)
    (hVpar : ∀ x ∈ K, ∀ (i : Fin (m + 1)) (U : Set (Work.Drive.Amb m)) (η : ℝ → Work.Drive.Amb m),
        IsOpen U → x ∈ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η → (∀ t : ℝ, η t i = 0) →
        (∀ y ∈ U, (y ∈ Z ↔ y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i))) →
        ∃ c : ℝ, c ≠ 0 ∧ V x = c • (EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η (x i)) (1 : ℝ)))
    (hface : ∀ b ∈ K ∩ Submission.Drive.unitBoxBdry m,
        ∃ i : Fin (m + 1), (b i = 0 ∨ b i = 1) ∧
          (∀ j : Fin (m + 1), j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧ V b i ≠ 0)
    (hmapsTo : ∀ x ∈ K, ∀ t : ℝ,
        (∀ u ∈ Set.uIcc (0 : ℝ) t, Work.Drive.flowGen V hV hVs u x ∈ Submission.Drive.unitBox m) →
        Work.Drive.flowGen V hV hVs t x ∈ K) :
    (K ∩ Submission.Drive.unitBoxBdry m).Finite ∧
      Even ((K ∩ Submission.Drive.unitBoxBdry m).ncard) := by
  obtain ⟨Cov⟩ := exists_flowCover_of_localGraph hK hKZ hgra V hV hVs hVpar hmapsTo
  have heven : Even ((K ∩ Submission.Drive.unitBoxBdry m).ncard) :=
    even_ncard_boundary (driveSetup V hV hVs K hmapsTo) Cov hface
  have hisol : ∀ b ∈ K ∩ Submission.Drive.unitBoxBdry m, ∃ U : Set (Amb m),
      IsOpen U ∧ b ∈ U ∧ U ∩ (K ∩ Submission.Drive.unitBoxBdry m) ⊆ {b} :=
    fun b hb => isolated_of_localGraph hKZ hgra V hVpar hface hb.1 hb.2
  have hKc : IsCompact (K ∩ Submission.Drive.unitBoxBdry m) :=
    hK.inter_right (isClosed_unitBoxBdry m)
  exact ⟨finite_of_isCompact_of_isolated hKc hisol, heven⟩

end

end Work.Drive.ppIntrinsic
