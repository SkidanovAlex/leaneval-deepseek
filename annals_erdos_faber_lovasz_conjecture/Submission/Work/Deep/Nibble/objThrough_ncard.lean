import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.ObjDefs

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

/-!
# `𝓜.deg w` edge objects through `w`

`objThrough 𝓜 w` is the set of edge objects of the multi-hypergraph `𝓜` whose
vertex set contains `w`: the proper edges of `𝓜` containing `w` (one object
each), together with the `𝓜.singles w` copies of the singleton `{w}`
(`𝓜.singles w` of them, which are all the objects through `w` carried by the
second summand of `EdgeObj 𝓜`).  Hence its cardinality is exactly the degree
`𝓜.deg w = hdeg 𝓜.edges w + 𝓜.singles w`.

The only subtlety is that `EdgeObj 𝓜` is a *definition* (`def`), so the two
summands are not visible at the implicit transparency level at which `simp`
re-checks its goals; we therefore make it locally `reducible` for the duration
of the theorem, so that all the counting lemmas below apply to the two summands
of `EdgeObj 𝓜` directly. -/

set_option allowUnsafeReducibility true in
attribute [local reducible] EdgeObj in
theorem objThrough_ncard {n : ℕ} (𝓜 : ErdosFaberLovaszConjecture.MultiHypergraph n) (w : Fin n) :
    (ErdosFaberLovaszConjecture.objThrough 𝓜 w).ncard = 𝓜.deg w := by
  classical
  -- The proper edges of `𝓜` through `w`, viewed as edge objects.
  set Asub : Set {e : Set (Fin n) // e ∈ 𝓜.edges} := {e | w ∈ e.1} with hAsub
  -- The copies of the singleton `{w}`.
  set Bsub : Set {p : Fin n × ℕ // p.2 < 𝓜.singles p.1} := {p | p.1.1 = w} with hBsub
  -- `objThrough 𝓜 w` is the disjoint union of the two corresponding images.
  have hunion : objThrough 𝓜 w = Sum.inl '' Asub ∪ Sum.inr '' Bsub := by
    rw [hAsub, hBsub]
    ext x
    rcases x with e | p
    · simp [objThrough]
    · simp [objThrough, eq_comm]
  -- The second summand indexes `ℕ`-many copies at each vertex; through `w` the
  -- second coordinate is the number of the copy, so the set is `Iio (singles w)`.
  have hg : (fun p : {p : Fin n × ℕ // p.2 < 𝓜.singles p.1} => p.1.2) '' Bsub
      = Set.Iio (𝓜.singles w) := by
    rw [hBsub]
    ext k
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [← hp]
      exact p.2
    · intro hk
      exact ⟨⟨(w, k), by simpa using hk⟩, by simp, rfl⟩
  have hginj : Set.InjOn (fun p : {p : Fin n × ℕ // p.2 < 𝓜.singles p.1} => p.1.2) Bsub := by
    intro p hp q hq hpq
    rw [hBsub] at hp hq
    exact Subtype.ext (Prod.ext (hp.trans hq.symm) hpq)
  -- The proper edges through `w`: `Asub` is the subtype counterpart of
  -- `{e ∈ 𝓜.edges | w ∈ e}` whose cardinality is `hdeg 𝓜.edges w`.
  have hA : Asub.ncard = MultiHypergraph.hdeg 𝓜.edges w := by
    have h1 : (Subtype.val '' Asub : Set (Set (Fin n))).ncard = Asub.ncard :=
      Set.ncard_image_of_injective _ Subtype.coe_injective
    have h2 : (Subtype.val '' Asub : Set (Set (Fin n))) = {e ∈ 𝓜.edges | w ∈ e} := by
      ext e
      constructor
      · rintro ⟨e', he', rfl⟩
        exact ⟨e'.2, by simpa [hAsub] using he'⟩
      · rintro ⟨heE, hwe⟩
        exact ⟨⟨e, heE⟩, by simpa [hAsub], rfl⟩
    simp only [MultiHypergraph.hdeg]
    rw [← h1, h2]
  have hB : Bsub.ncard = 𝓜.singles w := by
    have h1 := (Set.InjOn.ncard_image hginj).symm
    rw [h1, hg, Set.ncard_Iio_nat]
  have hBsub_fin : Bsub.Finite := by
    refine Set.Finite.of_finite_image
      (f := fun p : {p : Fin n × ℕ // p.2 < 𝓜.singles p.1} => p.1.2) ?_ hginj
    rw [hg]
    exact Set.finite_Iio _
  have hfinA : (Sum.inl '' Asub : Set (EdgeObj 𝓜)).Finite :=
    Set.Finite.image (f := fun e : {e : Set (Fin n) // e ∈ 𝓜.edges} => (Sum.inl e : EdgeObj 𝓜))
      (Set.Finite.subset Set.finite_univ (Set.subset_univ Asub))
  have hfinB : (Sum.inr '' Bsub : Set (EdgeObj 𝓜)).Finite :=
    Set.Finite.image
      (f := fun p : {p : Fin n × ℕ // p.2 < 𝓜.singles p.1} => (Sum.inr p : EdgeObj 𝓜)) hBsub_fin
  have hdisj : Disjoint (Sum.inl '' Asub : Set (EdgeObj 𝓜)) (Sum.inr '' Bsub : Set (EdgeObj 𝓜)) := by
    rw [Set.disjoint_left]
    rintro x ⟨e, -, rfl⟩ ⟨p, -, hp⟩
    exact Sum.inr_ne_inl hp
  rw [hunion, Set.ncard_union_eq hdisj hfinA hfinB,
      Set.ncard_image_of_injective _ EdgeObj.inl_injective,
      Set.ncard_image_of_injective _ EdgeObj.inr_injective,
      hA, hB, MultiHypergraph.deg_def]

end Work.Deep.Nibble
