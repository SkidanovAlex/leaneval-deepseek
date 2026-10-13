import Submission.Work.DSEQP.Term.QuotAway.Defs

universe a

namespace Work.DSEQP.Term.QuotAway.ChartImage

open MvPolynomial

variable {A : Type a} [CommRing A] {N : ℕ} {X : AlgebraicGeometry.Scheme.{a}}

/-- computation of `kappa` on the generators of `degZero (Jgr i) S`. -/
lemma kappa_divPow (i : X ⟶ DSMap.PSpace A N) (S : Finset (Fin (N + 1))) (k : ℕ)
    (f : MvPolynomial (Fin (N + 1)) A)
    (hf : f ∈ Work.DSCOH.homSub A (N + 1) (k * S.card)) (hJ : f ∈ Work.DSEQP.Jvan i) :
    Work.DSEQP.Term.kappa (A := A) (N := N) i S
      ⟨Work.DSCOH.divPow (A := A) (M := ↥(Work.DSEQP.Jvan i)) S k
          (Work.DSCOH.toLoc (A := A) (M := ↥(Work.DSEQP.Jvan i)) S ⟨f, hJ⟩),
        Work.DSCOH.divPow_toLoc_mem (A := A) (n := N + 1)
          (Work.DSEQP.Term.Jgr (A := A) (N := N) i) S k
          (Work.DSEQP.Term.mem_Jgr.mpr hf)⟩ =
    ⟨Work.DSCOH.divPow (A := A) (M := MvPolynomial (Fin (N + 1)) A) S k
        (Work.DSCOH.toLoc (A := A) (M := MvPolynomial (Fin (N + 1)) A) S f),
      Work.DSCOH.divPow_toLoc_mem (A := A) (n := N + 1)
        (Work.DSCOH.homSub A (N + 1)) S k hf⟩ := by
  apply Subtype.ext
  rw [Work.DSEQP.Term.kappa_apply]
  exact Work.DSEQP.Term.locMapOf_divPow_toLoc' (A := A) (N := N)
    (Submodule.subtype (Work.DSEQP.Jvan i)) S k ⟨f, hJ⟩

/-- `toAway` of the `kappa` of a generator. -/
lemma toAway_kappa_divPow (i : X ⟶ DSMap.PSpace A N) (S : Finset (Fin (N + 1))) (k : ℕ)
    (f : MvPolynomial (Fin (N + 1)) A)
    (hf : f ∈ Work.DSCOH.homSub A (N + 1) (k * S.card)) (hJ : f ∈ Work.DSEQP.Jvan i) :
    Work.DSEQP.DZA.toAway (A := A) (N := N) S
      (Work.DSEQP.Term.kappa (A := A) (N := N) i S
        ⟨Work.DSCOH.divPow (A := A) (M := ↥(Work.DSEQP.Jvan i)) S k
            (Work.DSCOH.toLoc (A := A) (M := ↥(Work.DSEQP.Jvan i)) S ⟨f, hJ⟩),
          Work.DSCOH.divPow_toLoc_mem (A := A) (n := N + 1)
            (Work.DSEQP.Term.Jgr (A := A) (N := N) i) S k
            (Work.DSEQP.Term.mem_Jgr.mpr hf)⟩) =
    HomogeneousLocalization.Away.mk (DSMap.PGr A N) (Work.DSEQP.xS_mem_homSub S) k f hf := by
  rw [ChartImage.kappa_divPow (A := A) (N := N) i S k f hf hJ]
  exact Work.DSEQP.DZA.toAway_apply_repr (A := A) (N := N) S _ hf rfl

/-- The image of `Img i S` under `toAway` is contained in the chart ideal. -/
lemma toAway_image_le_chartJ (i : X ⟶ DSMap.PSpace A N) (S : Finset (Fin (N + 1)))
    {y : ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := MvPolynomial (Fin (N + 1)) A)
      (Work.DSCOH.homSub A (N + 1)) S)}
    (hy : y ∈ Work.DSEQP.Term.Img (A := A) (N := N) i S) :
    Work.DSEQP.DZA.toAway (A := A) (N := N) S y ∈ Work.DSEQP.chartJ i S := by
  obtain ⟨x, rfl⟩ := Work.DSEQP.Term.mem_Img (A := A) (N := N) i hy
  obtain ⟨k, m, hm, hxr⟩ := Work.DSCOH.degZero_exists_repr (A := A) (n := N + 1)
    (M := ↥(Work.DSEQP.Jvan i)) (Work.DSEQP.Term.Jgr (A := A) (N := N) i) S x.2
  have hxk : x = ⟨Work.DSCOH.divPow (A := A) (M := ↥(Work.DSEQP.Jvan i)) S k
      (Work.DSCOH.toLoc (A := A) (M := ↥(Work.DSEQP.Jvan i)) S m),
      Work.DSCOH.divPow_toLoc_mem (A := A) (n := N + 1)
        (Work.DSEQP.Term.Jgr (A := A) (N := N) i) S k hm⟩ := Subtype.ext hxr
  rw [hxk, ChartImage.toAway_kappa_divPow (A := A) (N := N) i S k
    (m : MvPolynomial (Fin (N + 1)) A) (Work.DSEQP.Term.mem_Jgr.mp hm) m.2]
  exact Ideal.subset_span ⟨k, (m : MvPolynomial (Fin (N + 1)) A),
    Work.DSEQP.Term.mem_Jgr.mp hm, m.2,
    congrArg (fun pr => HomogeneousLocalization.Away.mk (DSMap.PGr A N)
      (Work.DSEQP.xS_mem_homSub S) k (m : MvPolynomial (Fin (N + 1)) A) pr)
      (Subsingleton.elim _ _)⟩

/-- The chart ideal is contained in the image of `Img i S` under `toAway`. -/
lemma chartJ_le_toAway_image (i : X ⟶ DSMap.PSpace A N) (S : Finset (Fin (N + 1))) :
    ∀ z ∈ Work.DSEQP.chartJ i S,
      ∃ y ∈ Work.DSEQP.Term.Img (A := A) (N := N) i S,
        Work.DSEQP.DZA.toAway (A := A) (N := N) S y = z := by
  have hmul : ∀ r : HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S),
      ∀ z ∈ Submodule.map (Work.DSEQP.DZA.toAway (A := A) (N := N) S)
        (Work.DSEQP.Term.Img (A := A) (N := N) i S),
      r * z ∈ Submodule.map (Work.DSEQP.DZA.toAway (A := A) (N := N) S)
        (Work.DSEQP.Term.Img (A := A) (N := N) i S) := by
    intro r z hz
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
    obtain ⟨x, rfl⟩ := Work.DSEQP.Term.mem_Img (A := A) (N := N) i hy
    obtain ⟨k, m, hm, hxr⟩ := Work.DSCOH.degZero_exists_repr (A := A) (n := N + 1)
      (M := ↥(Work.DSEQP.Jvan i)) (Work.DSEQP.Term.Jgr (A := A) (N := N) i) S x.2
    have hxk : x = ⟨Work.DSCOH.divPow (A := A) (M := ↥(Work.DSEQP.Jvan i)) S k
        (Work.DSCOH.toLoc (A := A) (M := ↥(Work.DSEQP.Jvan i)) S m),
        Work.DSCOH.divPow_toLoc_mem (A := A) (n := N + 1)
          (Work.DSEQP.Term.Jgr (A := A) (N := N) i) S k hm⟩ := Subtype.ext hxr
    obtain ⟨l, a, ha, hr⟩ := HomogeneousLocalization.Away.mk_surjective
      (𝒜 := DSMap.PGr A N) (f := Work.DSEQP.xS (A := A) S) (Work.DSEQP.xS_mem_homSub S) r
    have hgre : a * (m : MvPolynomial (Fin (N + 1)) A) ∈
        Work.DSCOH.homSub A (N + 1) ((l + k) * S.card) := by
      have h := SetLike.mul_mem_graded ha (Work.DSEQP.Term.mem_Jgr.mp hm)
      simpa only [smul_eq_mul, Nat.add_mul] using h
    rw [← hr, hxk, ChartImage.toAway_kappa_divPow (A := A) (N := N) i S k
      (m : MvPolynomial (Fin (N + 1)) A) (Work.DSEQP.Term.mem_Jgr.mp hm) m.2]
    rw [Work.DSEQP.DZA.away_mk_mul (A := A) (N := N) (Work.DSEQP.xS_mem_homSub S) l k a
      (m : MvPolynomial (Fin (N + 1)) A) ha (Work.DSEQP.Term.mem_Jgr.mp hm) hgre]
    refine Submodule.mem_map.mpr ⟨Work.DSEQP.Term.kappa (A := A) (N := N) i S
      ⟨Work.DSCOH.divPow (A := A) (M := ↥(Work.DSEQP.Jvan i)) S (l + k)
          (Work.DSCOH.toLoc (A := A) (M := ↥(Work.DSEQP.Jvan i)) S
            ⟨a * (m : MvPolynomial (Fin (N + 1)) A), Ideal.mul_mem_left _ a m.2⟩),
        Work.DSCOH.divPow_toLoc_mem (A := A) (n := N + 1)
          (Work.DSEQP.Term.Jgr (A := A) (N := N) i) S (l + k)
          (Work.DSEQP.Term.mem_Jgr.mpr hgre)⟩,
      Work.DSEQP.Term.kappa_mem_Img (A := A) (N := N) i S _, ?_⟩
    rw [ChartImage.toAway_kappa_divPow (A := A) (N := N) i S (l + k)
      (a * (m : MvPolynomial (Fin (N + 1)) A)) hgre (Ideal.mul_mem_left _ a m.2)]
  let QI : Submodule (HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S))
      (HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)) :=
    { carrier := (Submodule.map (Work.DSEQP.DZA.toAway (A := A) (N := N) S)
        (Work.DSEQP.Term.Img (A := A) (N := N) i S) : Set _)
      zero_mem' := (Submodule.map (Work.DSEQP.DZA.toAway (A := A) (N := N) S)
        (Work.DSEQP.Term.Img (A := A) (N := N) i S)).zero_mem
      add_mem' := fun hx hy => (Submodule.map (Work.DSEQP.DZA.toAway (A := A) (N := N) S)
        (Work.DSEQP.Term.Img (A := A) (N := N) i S)).add_mem hx hy
      smul_mem' := fun r x hx => hmul r x hx }
  have hle : Work.DSEQP.chartJ i S ≤ QI := by
    refine Ideal.span_le.mpr fun z hz => ?_
    obtain ⟨k, f, hf, hJ, rfl⟩ := hz
    exact Submodule.mem_map.mpr ⟨Work.DSEQP.Term.kappa (A := A) (N := N) i S
        ⟨Work.DSCOH.divPow (A := A) (M := ↥(Work.DSEQP.Jvan i)) S k
            (Work.DSCOH.toLoc (A := A) (M := ↥(Work.DSEQP.Jvan i)) S ⟨f, hJ⟩),
          Work.DSCOH.divPow_toLoc_mem (A := A) (n := N + 1)
            (Work.DSEQP.Term.Jgr (A := A) (N := N) i) S k
            (Work.DSEQP.Term.mem_Jgr.mpr hf)⟩,
      Work.DSEQP.Term.kappa_mem_Img (A := A) (N := N) i S _,
      (ChartImage.toAway_kappa_divPow (A := A) (N := N) i S k f hf hJ).trans
        (congrArg (fun pr => HomogeneousLocalization.Away.mk (DSMap.PGr A N)
          (Work.DSEQP.xS_mem_homSub S) k f pr) (Subsingleton.elim _ _)).symm⟩
  intro z hz
  exact Submodule.mem_map.mp (hle hz)

/-- **The chart ideal is the image of the kernel of `psi` under `toAway`** (as submodules). -/
theorem chartJA_eq_toAway_image (i : X ⟶ DSMap.PSpace A N) (S : Finset (Fin (N + 1))) :
    Work.DSEQP.Term.chartJA (A := A) (N := N) i S =
      Submodule.map (Work.DSEQP.DZA.toAway (A := A) (N := N) S)
        (Work.DSEQP.Term.Img (A := A) (N := N) i S) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨y, hy, hyz⟩ := chartJ_le_toAway_image (A := A) (N := N) i S z hz
    exact Submodule.mem_map.mpr ⟨y, hy, hyz⟩
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
    exact toAway_image_le_chartJ (A := A) (N := N) i S hy

/-- **The chart ideal is the image of the kernel of `psi` under `toAway`** (as sets). -/
theorem chartJ_eq_toAway_image (i : X ⟶ DSMap.PSpace A N) (S : Finset (Fin (N + 1))) :
    (Work.DSEQP.chartJ i S : Set (HomogeneousLocalization.Away (DSMap.PGr A N)
        (Work.DSEQP.xS (A := A) S))) =
      (Submodule.map (Work.DSEQP.DZA.toAway (A := A) (N := N) S)
        (Work.DSEQP.Term.Img (A := A) (N := N) i S) : Set _) := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, hyz⟩ := chartJ_le_toAway_image (A := A) (N := N) i S z hz
    exact ⟨y, hy, hyz⟩
  · rintro ⟨y, hy, hyz⟩
    rw [← hyz]
    exact toAway_image_le_chartJ (A := A) (N := N) i S hy

end Work.DSEQP.Term.QuotAway.ChartImage
