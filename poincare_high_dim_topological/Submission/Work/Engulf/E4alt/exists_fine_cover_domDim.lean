import Mathlib
import Submission.Work.PL.Defs

namespace Work.Engulf.E4alt

open Set Metric
open scoped Pointwise Convex

/-- **A small relative simplex.**  If `x` lies in an affine subspace `F`, then for every `η > 0`
there is a finite vertex set `t ⊆ F` with exactly `finrank ℝ F.direction + 1` vertices whose
simplex `PL.simp t` contains a relative ball around `x` (in `F`) and is contained in the ball
`ball x η`. -/
lemma exists_simplex_rel {m : ℕ} (F : AffineSubspace ℝ (PL.E m)) (x : PL.E m) (hx : x ∈ F)
    (η : ℝ) (hη : 0 < η) :
    ∃ t : Finset (PL.E m), (↑t : Set (PL.E m)) ⊆ (F : Set (PL.E m)) ∧
      t.card = Module.finrank ℝ F.direction + 1 ∧
      (∃ ρ > 0, ∀ y, dist y x < ρ → y ∈ F → y ∈ PL.simp t) ∧
      PL.simp t ⊆ ball x η := by
  classical
  have hη3 : (0:ℝ) < η/3 := by linarith
  obtain ⟨b, hb_int, hb_sub⟩ :=
    exists_mem_interior_convexHull_affineBasis (E := ↥F.direction) (x := 0)
      (s := ball (0 : ↥F.direction) (η/3)) (ball_mem_nhds 0 hη3)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hb_int)
  set t : Finset (PL.E m) := Finset.univ.image (fun i => x + (b i : PL.E m)) with ht
  have hinj : Function.Injective (fun i => x + (b i : PL.E m)) := by
    intro i j hij
    apply b.ind.injective
    apply Subtype.ext
    have h2 := congrArg (fun z : PL.E m => z - x) hij
    simpa using h2
  have hcard : t.card = Module.finrank ℝ F.direction + 1 := by
    rw [ht, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have htF : (↑t : Set (PL.E m)) ⊆ (F : Set (PL.E m)) := by
    intro y hy
    rw [ht, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
    obtain ⟨i, rfl⟩ := hy
    have := AffineSubspace.vadd_mem_of_mem_direction (b i).2 hx
    simpa [vadd_eq_add, add_comm] using this
  have hset : (↑t : Set (PL.E m)) = x +ᵥ (Subtype.val '' range b) := by
    rw [ht]
    ext z
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_vadd_set]
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨↑(b a), Set.mem_image_of_mem _ (Set.mem_range_self a), ?_⟩
      simp [vadd_eq_add]
    · rintro ⟨y, hy, hyz⟩
      rw [Set.mem_image] at hy
      obtain ⟨v, hv, hvy⟩ := hy
      rw [Set.mem_range] at hv
      obtain ⟨a, rfl⟩ := hv
      refine ⟨a, ?_⟩
      rw [← hvy] at hyz
      simpa [vadd_eq_add] using hyz
  have hball : ∃ ρ > 0, ∀ y, dist y x < ρ → y ∈ F → y ∈ PL.simp t := by
    refine ⟨ε, hε, ?_⟩
    intro y hyρ hyF
    have hyV : y - x ∈ F.direction := by
      rw [← vsub_eq_sub]; exact AffineSubspace.vsub_mem_direction hyF hx
    set w : ↥F.direction := ⟨y - x, hyV⟩ with hw
    have hw_norm : ‖w‖ < ε := by
      rw [← Submodule.norm_coe]
      simpa [hw, dist_eq_norm] using hyρ
    have hw_mem : w ∈ convexHull ℝ (range b) := hεsub (by simpa [mem_ball] using hw_norm)
    have hw_in : (w : PL.E m) ∈ convexHull ℝ (Subtype.val '' range b) := by
      have hh := LinearMap.image_convexHull (Submodule.subtype F.direction) (range b)
      rw [Submodule.coe_subtype] at hh
      rw [← hh]
      exact ⟨w, hw_mem, rfl⟩
    have hy_eq : y = x + (w : PL.E m) := by
      simp [hw]
    rw [PL.simp, hset, convexHull_vadd]
    exact ⟨(w : PL.E m), hw_in, by simp [hy_eq, vadd_eq_add]⟩
  refine ⟨t, htF, hcard, hball, ?_⟩
  rw [PL.simp, hset]
  apply convexHull_min _ (convex_ball x η)
  rintro z ⟨w, hw, rfl⟩
  rw [Set.mem_image] at hw
  obtain ⟨v, hv, hvw⟩ := hw
  rw [Set.mem_range] at hv
  obtain ⟨i, rfl⟩ := hv
  rw [← hvw]
  have h2 := hb_sub (subset_convexHull ℝ (range b) (Set.mem_range_self (f := ⇑b) i))
  rw [mem_ball, dist_eq_norm, sub_zero] at h2
  rw [mem_ball, dist_eq_norm]
  simp only [vadd_eq_add, add_sub_cancel_left]
  rw [Submodule.norm_coe]
  linarith

/-- **A fine `DomDim` cover.**  If `A ⊆ ℝᵐ` is `d`-dominated (`PL.DomDim A d`: covered by
finitely many simplices with at most `d + 1` vertices), then for every `η > 0` there is a finite
family `T` of vertex sets with at most `d + 1` vertices whose simplices still cover `A`, and such
that every simplex `PL.simp t`, `t ∈ T`, is contained in the `η`-ball about some point `a ∈ A`.
(`T = ∅` when `A = ∅`.)

Route.  Write `hA` as `A ⊆ ⋃ s ∈ S, simp s` with `s.card ≤ d + 1`.  Each compact set
`K_s := closure A ∩ simp s` lies in the affine subspace `F_s := affineSpan ℝ (s : Set (E m))`,
whose direction has `finrank ≤ s.card - 1 ≤ d` (`direction_affineSpan`,
`finrank_vectorSpan_image_finset_le`).  For `x ∈ K_s` work in the finite-dimensional vector
space `↥F_s.direction`: `exists_mem_interior_convexHull_affineBasis` applied at `0` with the
neighbourhood `ball 0 (η/3)` yields an affine basis of the direction, hence a simplex `t_x ⊆ F_s`
with `t_x.card ≤ finrank + 1 ≤ d + 1` and `x ∈ interior (convexHull t_x)` *relative to* `F_s`,
all of `convexHull t_x` within `η/3` of `x`.  Therefore `ball x ρ ⊆ ⋃` for some `ρ > 0`, and a
finite subcover of `K_s` by such relative balls (`IsCompact.elim_finite_subcover` /
`IsCompact.isTotallyBounded`) gives finitely many `x`'s.  Finally `dist x A = 0` for
`x ∈ closure A`, so each `convexHull t_x` also lies in the `η`-ball about a point of `A`. -/
theorem exists_fine_cover_domDim {m : ℕ} {A : Set (PL.E m)} {d : ℤ}
    (hA : PL.DomDim A d) (η : ℝ) (hη : 0 < η) :
    ∃ T : Finset (Finset (PL.E m)),
      (∀ t ∈ T, (t.card : ℤ) ≤ d + 1) ∧
      A ⊆ ⋃ t ∈ T, PL.simp t ∧
      (∀ t ∈ T, ∃ a ∈ A, ∀ y ∈ PL.simp t, dist y a < η) := by
  classical
  have hη3 : (0:ℝ) < η/3 := by linarith
  obtain ⟨S, hScard, hScover⟩ := hA
  have hbuild : ∀ s : {s : Finset (PL.E m) // s ∈ S},
      ∃ Ts : Finset (Finset (PL.E m)),
        (∀ t ∈ Ts, (t.card : ℤ) ≤ d + 1) ∧
        (closure A ∩ PL.simp s.1 ⊆ ⋃ t ∈ Ts, PL.simp t) ∧
        (∀ t ∈ Ts, ∃ a ∈ A, ∀ y ∈ PL.simp t, dist y a < η) := by
    intro s
    set F : AffineSubspace ℝ (PL.E m) := affineSpan ℝ (s.1 : Set (PL.E m)) with hF
    have hKc : IsCompact (closure A ∩ PL.simp s.1) :=
      (Finite.isCompact_convexHull ℝ (Finset.finite_toSet s.1)).inter_left isClosed_closure
    have hKsubF : (closure A ∩ PL.simp s.1) ⊆ (F : Set (PL.E m)) := by
      intro y hy
      exact convexHull_subset_affineSpan (𝕜 := ℝ) (s.1 : Set (PL.E m)) hy.2
    have key : ∀ x : ↥(closure A ∩ PL.simp s.1), ∃ (t : Finset (PL.E m)) (ρ : ℝ),
        (t.card : ℤ) ≤ d + 1 ∧ 0 < ρ ∧
        (∀ y, dist y x.1 < ρ → y ∈ F → y ∈ PL.simp t) ∧
        PL.simp t ⊆ ball x.1 (η/3) := by
      intro x
      have hxF : x.1 ∈ F := convexHull_subset_affineSpan (𝕜 := ℝ) (s.1 : Set (PL.E m)) x.2.2
      obtain ⟨t, htF, htcard, ⟨ρ, hρ, hrel⟩, hsmall⟩ := exists_simplex_rel F x.1 hxF (η/3) hη3
      have hsne : s.1.Nonempty := by
        rcases Finset.eq_empty_or_nonempty s.1 with h | h
        · exfalso
          have hcoe : (↑s.1 : Set (PL.E m)) = ∅ := by rw [h]; simp
          have hsub : PL.simp s.1 ⊆ (∅ : Set (PL.E m)) := by
            intro y hy
            rw [PL.simp, hcoe, convexHull_empty] at hy
            exact hy
          exact hsub x.2.2
        · exact h
      have hcardpos : 0 < s.1.card := Finset.card_pos.mpr hsne
      have hspan : Module.finrank ℝ (vectorSpan ℝ ((s.1 : Finset (PL.E m)) : Set (PL.E m)))
          ≤ s.1.card - 1 := by
        have h := finrank_vectorSpan_image_finset_le (k := ℝ) (p := (id : PL.E m → PL.E m))
          (s := s.1) (n := s.1.card - 1) (by omega)
        have heq : (Finset.image (id : PL.E m → PL.E m) s.1 : Set (PL.E m))
            = (s.1 : Set (PL.E m)) := by simp
        rw [← heq]
        exact h
      have hdir : F.direction = vectorSpan ℝ ((s.1 : Finset (PL.E m)) : Set (PL.E m)) := by
        rw [hF]; exact direction_affineSpan ℝ (s.1 : Set (PL.E m))
      have hfin : Module.finrank ℝ F.direction ≤ s.1.card - 1 := by rw [hdir]; exact hspan
      refine ⟨t, ρ, ?_, hρ, hrel, hsmall⟩
      rw [htcard]
      have h2 := hScard s.1 s.2
      have hfin' : Module.finrank ℝ F.direction + 1 ≤ s.1.card := by omega
      have h1 : ((Module.finrank ℝ F.direction : ℤ) + 1) ≤ (s.1.card : ℤ) := by
        exact_mod_cast hfin'
      push_cast
      linarith
    let tf : ↥(closure A ∩ PL.simp s.1) → Finset (PL.E m) := fun x => (key x).choose
    let ρf : ↥(closure A ∩ PL.simp s.1) → ℝ := fun x => (key x).choose_spec.choose
    have hspec : ∀ x : ↥(closure A ∩ PL.simp s.1),
        ((tf x).card : ℤ) ≤ d + 1 ∧ 0 < ρf x ∧
        (∀ y, dist y x.1 < ρf x → y ∈ F → y ∈ PL.simp (tf x)) ∧
        PL.simp (tf x) ⊆ ball x.1 (η/3) := fun x => (key x).choose_spec.choose_spec
    obtain ⟨Fc, hFc⟩ := hKc.elim_finite_subcover
      (fun x : ↥(closure A ∩ PL.simp s.1) => ball x.1 (ρf x))
      (fun x => isOpen_ball)
      (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, by simpa [mem_ball] using (hspec ⟨y, hy⟩).2.1⟩)
    refine ⟨Fc.image tf, ?_, ?_, ?_⟩
    · intro t ht
      rw [Finset.mem_image] at ht
      obtain ⟨x, -, rfl⟩ := ht
      exact (hspec x).1
    · intro y hy
      obtain ⟨x, hxFc, hyx⟩ := Set.mem_iUnion₂.mp (hFc hy)
      refine Set.mem_iUnion₂.mpr ⟨tf x, Finset.mem_image_of_mem tf hxFc, ?_⟩
      exact (hspec x).2.2.1 y hyx (hKsubF hy)
    · intro t ht
      rw [Finset.mem_image] at ht
      obtain ⟨x, -, rfl⟩ := ht
      obtain ⟨a, haA, hda⟩ := Metric.mem_closure_iff.mp x.2.1 (η/3) hη3
      refine ⟨a, haA, ?_⟩
      intro y hy
      have hyx : dist y x.1 < η/3 := by
        have hh := (hspec x).2.2.2 hy
        rwa [mem_ball] at hh
      calc dist y a ≤ dist y x.1 + dist x.1 a := dist_triangle _ _ _
        _ < η/3 + η/3 := by linarith
        _ < η := by linarith
  let Ts : {s : Finset (PL.E m) // s ∈ S} → Finset (Finset (PL.E m)) := fun s => (hbuild s).choose
  refine ⟨S.attach.biUnion Ts, ?_, ?_, ?_⟩
  · intro t ht
    rw [Finset.mem_biUnion] at ht
    obtain ⟨s, -, hts⟩ := ht
    exact ((hbuild s).choose_spec).1 t hts
  · intro a ha
    obtain ⟨s, hsS, has⟩ := Set.mem_iUnion₂.mp (hScover ha)
    have hKa : a ∈ closure A ∩ PL.simp s := ⟨subset_closure ha, has⟩
    obtain ⟨t, htTs, hat⟩ := Set.mem_iUnion₂.mp (((hbuild ⟨s, hsS⟩).choose_spec).2.1 hKa)
    exact Set.mem_iUnion₂.mpr
      ⟨t, Finset.mem_biUnion.mpr ⟨⟨s, hsS⟩, Finset.mem_attach S ⟨s, hsS⟩, htTs⟩, hat⟩
  · intro t ht
    rw [Finset.mem_biUnion] at ht
    obtain ⟨s, -, hts⟩ := ht
    exact ((hbuild s).choose_spec).2.2 t hts

end Work.Engulf.E4alt
