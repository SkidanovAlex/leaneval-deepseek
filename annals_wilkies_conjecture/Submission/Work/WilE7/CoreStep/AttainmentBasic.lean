/-
  Area E7 / `CoreLT_succ`, the vertical row: the **reduction of the attainment dichotomy** to a
  pointwise statement about the frontier of `T`.

  Setting: `T : Stratum 0 (n + (m+1))` (an absolute piece), a set `C : Set (Fin n → ℝ)` of base
  points, and a level function `ℓ : (Fin n → ℝ) → ℝ`.  Write

  `Attain T C ℓ := {x ∈ C : ∃ z ∈ T.X.set, projTop (absPt z) = Fin.snoc x (ℓ x)}`

  ("the level `ℓ` is attained on the fibre of `T` over `x`").

  * `attainSet_eq_univ_of_forall` — if the level is attained at every base point, the attainment
    set is all of `C` (the `S ⊆ T` case of the vertical row);
  * `eventually_not_attain_of_no_witness` — **(P2′)** if *no* frontier point of `T` over `C` lies on
    the graph of `ℓ` (no "frontier witness"), then the set of *non*-attainment is relatively open in
    `C` — i.e. the attainment set is relatively closed.

  The proof is the compactness argument: witnesses `z_k` over base points `x_k → x₀` have a
  convergent subsequence inside the compact cube `cubeC (n+(m+1))`; the limit `w` lies over
  `(x₀, ℓ x₀)` and in `closure (absSet T)`, so `hno` puts it in `absSet T`, exhibiting an attainment
  at `x₀`.

  The remaining mathematical input of the vertical row (see `NOTES_S53_span_pieces_and_levels.md`
  §4) is exactly the exclusion of the frontier witness, i.e. the hypothesis `hno` below; the
  openness half `(P1)` is the PROVED `attainment_open`.
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.ProjTopDefs
import Submission.Work.CoreStep.pairCovers_of_no_lowDim
import Submission.Work.WilE7.DecompDefs

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.WilE7.CoreStep

open WilkiesDesign WilkiesDesign.E

/-- The set of base points (inside `C`) over which the level `ℓ` is attained on the fibres of `T`. -/
def AttainSet {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (C : Set (Fin n → ℝ)) (ℓ : (Fin n → ℝ) → ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ C ∧ ∃ z ∈ T.X.set,
    Work.WilE7.CoreStep.projTop n m (Work.WilE7.MainDesign.absPt z) = Fin.snoc x (ℓ x)}

theorem mem_AttainSet {n m : ℕ} {T : WilkiesDesign.E.Stratum 0 (n + (m + 1))}
    {C : Set (Fin n → ℝ)} {ℓ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} :
    x ∈ AttainSet T C ℓ ↔ x ∈ C ∧ ∃ z ∈ T.X.set,
      Work.WilE7.CoreStep.projTop n m (Work.WilE7.MainDesign.absPt z) = Fin.snoc x (ℓ x) :=
  Iff.rfl

/-- The pointwise form of attainment at `x`. -/
def AttainAt {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (ℓ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Prop :=
  ∃ z ∈ T.X.set,
    Work.WilE7.CoreStep.projTop n m (Work.WilE7.MainDesign.absPt z) = Fin.snoc x (ℓ x)

theorem mem_AttainSet_iff {n m : ℕ} {T : WilkiesDesign.E.Stratum 0 (n + (m + 1))}
    {C : Set (Fin n → ℝ)} {ℓ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} :
    x ∈ AttainSet T C ℓ ↔ x ∈ C ∧ AttainAt T ℓ x :=
  Iff.rfl

/-- `AttainAt` is unchanged if the level is replaced by any function agreeing with it at `x`. -/
theorem attainAt_congr {n m : ℕ} {T : WilkiesDesign.E.Stratum 0 (n + (m + 1))}
    {ℓ ℓ' : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (h : ℓ x = ℓ' x) :
    AttainAt T ℓ x ↔ AttainAt T ℓ' x := by
  simp only [AttainAt, h]

/-- The `S ⊆ T` case of the vertical row: if the level is attained at every base point of `C`,
then the attainment set is all of `C`. -/
theorem attainSet_eq_univ_of_forall {n m : ℕ} {T : WilkiesDesign.E.Stratum 0 (n + (m + 1))}
    {C : Set (Fin n → ℝ)} {ℓ : (Fin n → ℝ) → ℝ}
    (h : ∀ x ∈ C, AttainAt T ℓ x) :
    ∀ x, x ∈ AttainSet T C ℓ ↔ x ∈ C := by
  intro x
  rw [mem_AttainSet_iff]
  exact ⟨fun hx => hx.1, fun hx => ⟨hx, h x hx⟩⟩

/-- **(P2′).**  If no frontier point of `T` over `C` lies on the graph of the level `ℓ`, then the
non-attainment is relatively open in `C`. -/
theorem eventually_not_attain_of_no_witness {n m : ℕ}
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (C : Set (Fin n → ℝ)) (ℓ : (Fin n → ℝ) → ℝ) (hℓ : ContinuousOn ℓ C)
    (hno : ∀ x ∈ C, ∀ p ∈ closure (Work.WilE7.MainDesign.absSet T),
      Work.WilE7.CoreStep.projTop n m p = Fin.snoc x (ℓ x) →
        p ∈ Work.WilE7.MainDesign.absSet T) :
    ∀ x₀ ∈ C, ¬ AttainAt T ℓ x₀ → ∀ᶠ x in 𝓝[C] x₀, ¬ AttainAt T ℓ x := by
  intro x₀ hx₀ hx₀not
  rw [eventually_nhdsWithin_iff]
  by_contra hcon
  have hfail : ∀ U ∈ 𝓝 x₀, ∃ x ∈ U, x ∈ C ∧ AttainAt T ℓ x := by
    intro U hU
    by_contra hh
    refine hcon (Filter.mem_of_superset hU ?_)
    intro x hx
    simp only [Set.mem_setOf_eq]
    intro hxC hxAtt
    exact hh ⟨x, hx, ⟨hxC, hxAtt⟩⟩
  have hsel : ∀ k : ℕ, ∃ x : Fin n → ℝ, dist x x₀ < ((k : ℝ) + 1)⁻¹ ∧ x ∈ C ∧ AttainAt T ℓ x := by
    intro k
    obtain ⟨x, hxball, hx⟩ := hfail (Metric.ball x₀ ((k : ℝ) + 1)⁻¹)
      (Metric.ball_mem_nhds x₀ (by positivity))
    exact ⟨x, Metric.mem_ball.mp hxball, hx⟩
  choose x hxball hxC hxAtt using hsel
  -- the base points converge to `x₀`
  have hx_tend : Tendsto (fun k : ℕ => x k) atTop (𝓝 x₀) := by
    refine Metric.tendsto_atTop.mpr fun ε hε => ?_
    obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
    refine ⟨K, fun k hk => ?_⟩
    have h1 : dist (x k) x₀ < ((k : ℝ) + 1)⁻¹ := hxball k
    have h1' : dist (x k) x₀ < 1 / ((k : ℝ) + 1) := by simpa only [one_div] using h1
    have h2 : 1 / ((k : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hk)
    exact lt_of_lt_of_le (h1'.trans_le h2) (le_of_lt hK)
  -- witnesses
  choose z hz hzπ using fun k : ℕ => hxAtt k
  have hw_mem : ∀ k : ℕ, Work.WilE7.MainDesign.absPt (z k) ∈
      WilkiesDesign.E.cubeC (n + (m + 1)) :=
    fun k => Work.CoreStep.absSet_subset_cubeC' T ⟨z k, hz k, rfl⟩
  obtain ⟨w, _hw_cube, φ, hφmono, hφtend⟩ :=
    (Work.CoreStep.cubeC_isCompact' (n + (m + 1))).tendsto_subseq hw_mem
  have hw_cl : w ∈ closure (Work.WilE7.MainDesign.absSet T) :=
    isClosed_closure.mem_of_tendsto hφtend
      (Filter.Eventually.of_forall fun k => subset_closure ⟨z (φ k), hz (φ k), rfl⟩)
  -- the level values converge to `ℓ x₀`
  have hxφ_tend : Tendsto (fun k : ℕ => x (φ k)) atTop (𝓝 x₀) :=
    hx_tend.comp hφmono.tendsto_atTop
  have hxφ_within : Tendsto (fun k : ℕ => x (φ k)) atTop (𝓝[C] x₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨hxφ_tend, Filter.Eventually.of_forall fun k => hxC (φ k)⟩
  have hlφ : Tendsto (fun k : ℕ => ℓ (x (φ k))) atTop (𝓝 (ℓ x₀)) :=
    (hℓ.continuousWithinAt hx₀).tendsto.comp hxφ_within
  have hsnoc : Tendsto (fun k : ℕ => Fin.snoc (x (φ k)) (ℓ (x (φ k))))
      atTop (𝓝 (Fin.snoc x₀ (ℓ x₀) : Fin (n + 1) → ℝ)) := by
    refine tendsto_pi_nhds.mpr fun i => ?_
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · simpa only [Fin.snoc_last] using hlφ
    · simpa only [Fin.snoc_castSucc, Function.comp_def] using
        (continuous_apply i').tendsto x₀ |>.comp hxφ_tend
  have hproj_tend : Tendsto
      (fun k : ℕ => Work.WilE7.CoreStep.projTop n m (Work.WilE7.MainDesign.absPt (z (φ k))))
      atTop (𝓝 (Work.WilE7.CoreStep.projTop n m w)) :=
    ((continuous_projTop n m).tendsto w).comp hφtend
  have hproj_tend' : Tendsto
      (fun k : ℕ => Work.WilE7.CoreStep.projTop n m (Work.WilE7.MainDesign.absPt (z (φ k))))
      atTop (𝓝 (Fin.snoc x₀ (ℓ x₀) : Fin (n + 1) → ℝ)) :=
    hsnoc.congr' (Filter.Eventually.of_forall fun k => (hzπ (φ k)).symm)
  have hproj_w : Work.WilE7.CoreStep.projTop n m w =
      Fin.snoc x₀ (ℓ x₀) :=
    tendsto_nhds_unique hproj_tend hproj_tend'
  have hw_A : w ∈ Work.WilE7.MainDesign.absSet T := hno x₀ hx₀ w hw_cl hproj_w
  obtain ⟨z₀, hz₀, hz₀eq⟩ := hw_A
  exact hx₀not ⟨z₀, hz₀, by rw [hz₀eq, hproj_w]⟩

/-- **Classification of a frontier witness.**  If a point `p` of `closure (absSet T) ∩ absSet S'`
lies over the graph of the level `ℓ` at `x ∈ C`, and `S'` carries sheets `s'` over `C` which cover
its fibres, then some sheet of `S'` has level `≡ ℓ` on all of `C` — *provided* the level dichotomy
(agreement at a point of `C` propagates to all of `C`) is available for the pair `(sheet j, ℓ)`.

So a frontier witness can only occur for a level which is *identically* a frontier sheet level. -/
theorem exists_sheet_eq_of_witness {n m k' : ℕ}
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (C : Set (Fin n → ℝ))
    (ℓ : (Fin n → ℝ) → ℝ)
    (S' : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (s' : Fin k' → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hcov' : ∀ z ∈ Work.WilE7.MainDesign.absSet S',
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C →
      ∃ j : Fin k', s' j (WilkiesDesign.E.projFirst n (m + 1) z) =
        WilkiesDesign.E.projSnd n (m + 1) z)
    (hdich : ∀ (j : Fin k') (x y : Fin n → ℝ), x ∈ C → y ∈ C →
      (s' j x) (Fin.last m) = ℓ x → (s' j y) (Fin.last m) = ℓ y)
    {x : Fin n → ℝ} (hx : x ∈ C)
    {p : Fin (n + (m + 1)) → ℝ}
    (hpS : p ∈ Work.WilE7.MainDesign.absSet S')
    (hproj : Work.WilE7.CoreStep.projTop n m p = Fin.snoc x (ℓ x)) :
    ∃ j : Fin k', ∀ y ∈ C, (s' j y) (Fin.last m) = ℓ y := by
  have hbase : WilkiesDesign.E.projFirst n (m + 1) p = x := by
    have h := congrArg Fin.init hproj
    rwa [Work.WilE7.CoreStep.projTop_init, Fin.init_snoc] at h
  obtain ⟨j, hj⟩ := hcov' p hpS (by rw [hbase]; exact hx)
  refine ⟨j, fun y hy => ?_⟩
  have hval : (s' j x) (Fin.last m) = ℓ x := by
    have h1 : (s' j x) (Fin.last m) = (WilkiesDesign.E.projSnd n (m + 1) p) (Fin.last m) := by
      rw [← hj, hbase]
    have h2 : (WilkiesDesign.E.projSnd n (m + 1) p) (Fin.last m) =
        (Work.WilE7.CoreStep.projTop n m p) (Fin.last n) :=
      (Work.WilE7.CoreStep.projTop_last n m p).symm
    rw [h1, h2, hproj, Fin.snoc_last]
  exact hdich j x y hx hy hval

/-- Wiring to the cell family: if a level is attained on all of `C`, its graph cell is contained in
`projTopSet T`; if it is attained nowhere on `C`, the graph cell misses `projTopSet T`. -/
theorem gr_subset_or_disjoint_of_attain {n m : ℕ}
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (C : Set (Fin n → ℝ)) (ℓ : (Fin n → ℝ) → ℝ)
    (h : ∀ x ∈ C, AttainAt T ℓ x) :
    Work.WilE7.gr C ℓ ⊆ Work.WilE7.CoreStep.projTopSet T := by
  rintro z ⟨hzC, hzlast⟩
  obtain ⟨w, hw, hweq⟩ := h (Fin.init z) hzC
  refine ⟨Work.WilE7.MainDesign.absPt w, ⟨w, hw, rfl⟩, ?_⟩
  rw [hweq, ← hzlast]
  exact Fin.snoc_init_self z

theorem gr_disjoint_of_not_attain {n m : ℕ}
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (C : Set (Fin n → ℝ)) (ℓ : (Fin n → ℝ) → ℝ)
    (h : ∀ x ∈ C, ¬ AttainAt T ℓ x) :
    Disjoint (Work.WilE7.gr C ℓ) (Work.WilE7.CoreStep.projTopSet T) := by
  rw [Set.disjoint_left]
  rintro z ⟨hzC, hzlast⟩ ⟨w, hw, hweq⟩
  obtain ⟨w', hw'X, hw'eq⟩ := hw
  refine h (Fin.init z) hzC ⟨w', hw'X, ?_⟩
  rw [hw'eq, hweq, ← hzlast]
  exact (Fin.snoc_init_self z).symm

/-- The per-level attainment dichotomy gives the `hgraph` input of
`Work.WilE7.CoreStep.cells_compat_levels` for the piece `T`: the graph cell restricted to the
cylinder is contained in `A = projTop T ∩ cyl C`, or disjoint from it. -/
theorem gr_inter_cyl_subset_or_disjoint_of_dichotomy {n m : ℕ}
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (C : Set (Fin n → ℝ)) (ℓ : (Fin n → ℝ) → ℝ)
    (h : (∀ x ∈ C, AttainAt T ℓ x) ∨ (∀ x ∈ C, ¬ AttainAt T ℓ x)) :
    (Work.WilE7.gr C ℓ ∩ Work.WilE7.cyl C ⊆
        Work.WilE7.CoreStep.projTopSet T ∩ Work.WilE7.cyl C) ∨
      Disjoint (Work.WilE7.gr C ℓ ∩ Work.WilE7.cyl C)
        (Work.WilE7.CoreStep.projTopSet T ∩ Work.WilE7.cyl C) := by
  rcases h with h | h
  · exact Or.inl (Set.inter_subset_inter_left _ (gr_subset_or_disjoint_of_attain T C ℓ h))
  · exact Or.inr (((gr_disjoint_of_not_attain T C ℓ h).mono_left Set.inter_subset_left).mono_right
      Set.inter_subset_left)

end Work.WilE7.CoreStep
