import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.ObjDefs
import Submission.Work.Deep.Nibble.objThrough_ncard

/-!
# `objCover`: colours missing a vertex, counted through the edge objects

Let `𝓜` be a multi-hypergraph on `Fin n` and let `N : Fin D → Set (EdgeObj 𝓜)`
be a family of **object matchings** (each `N c` consists of edge objects with
pairwise disjoint vertex sets; `IsObjMatching`).  Write

* `Cov  = {c | w ∈ objVert (N c)}` — the colours covering the vertex `w`,
* `A    = {c | w ∉ objVert (N c)}` — the colours missing `w`,
* `T    = objThrough 𝓜 w` — the `𝓜.deg w` edge objects through `w`,
* `Used = {x ∈ T | ∃ c, x ∈ N c}` — the objects through `w` used by some colour,
* `B    = {x ∈ T | ∀ c, x ∉ N c}` — the objects through `w` used by no colour.

Since within a single matching `N c` two distinct objects through `w` would
share `w` (contradicting `IsObjMatching`), each colour of `Cov` uses **at most
one** object through `w`, and every used object is used by a colour of `Cov`:

  `Used ⊆ ⋃_{c ∈ Cov} (N c ∩ T)`, with each `N c ∩ T` a subsingleton,

whence `Used.ncard ≤ Cov.ncard`.  As `A, Cov` partition `Fin D` and `B, Used`
partition `T` (of cardinality `𝓜.deg w`), this gives

  `|A| = D - |Cov| ≤ D - (|T| - |B|) = (D - 𝓜.deg w) + |B|`,

which is `objCover`: the number of colours not covering `w` is at most the
number of "missing" degrees of `w` plus the number of edge objects through `w`
left unused.

The counting of `Used.ncard ≤ Cov.ncard` is done without any choice principle:
the pairs `P = {(x,c) | x ∈ N c, w ∈ toSet x}` project *onto* `Used` under `fst`
and *injectively* into `Cov` under `snd` (by the matching property), so
`|Used| ≤ |P| = |snd '' P| ≤ |Cov|`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

/-- The edge objects of a multi-hypergraph `𝓜` form a **finite** type: the
proper edges are subsets of the finite set `Fin n`, and the copies of the
singleton `{v}` are indexed by `k < 𝓜.singles v`.

This is not found by instance search (the bound `k < 𝓜.singles v` is not
visible to the `Fintype` instance for `Fin n × ℕ`), so we record it. -/
theorem finite_edgeObj {n : ℕ} (𝓜 : MultiHypergraph n) : Finite (EdgeObj 𝓜) := by
  have h1 : Finite {e : Set (Fin n) // e ∈ 𝓜.edges} := inferInstance
  have h2 : Finite {p : Fin n × ℕ // p.2 < 𝓜.singles p.1} := by
    have h : Finite (Σ v : Fin n, Fin (𝓜.singles v)) := Finite.of_fintype _
    refine Finite.of_injective
      (fun p : {p : Fin n × ℕ // p.2 < 𝓜.singles p.1} =>
        (⟨p.1.1, ⟨p.1.2, p.2⟩⟩ : Σ v : Fin n, Fin (𝓜.singles v))) ?_
    intro p q hpq
    have h1 : p.1.1 = q.1.1 := congrArg Sigma.fst hpq
    have h2 : p.1.2 = q.1.2 :=
      congrArg (fun x : Σ v : Fin n, Fin (𝓜.singles v) => (x.2 : ℕ)) hpq
    exact Subtype.ext (Prod.ext h1 h2)
  haveI : Finite {e : Set (Fin n) // e ∈ 𝓜.edges} := h1
  haveI : Finite {p : Fin n × ℕ // p.2 < 𝓜.singles p.1} := h2
  show Finite ({e : Set (Fin n) // e ∈ 𝓜.edges} ⊕ {p : Fin n × ℕ // p.2 < 𝓜.singles p.1})
  infer_instance

/-- `w` lies in the vertex set covered by a family `N` of edge objects iff some
object of `N` has `w` in its vertex set. -/
theorem mem_objVert {n : ℕ} {𝓜 : MultiHypergraph n} {N : Set (EdgeObj 𝓜)} {w : Fin n} :
    (w ∈ objVert N) ↔ ∃ x ∈ N, w ∈ EdgeObj.toSet x := by
  simp [objVert]

/-- **The covering count of the §7 assembly.**  For a family of object matchings
`N : Fin D → Set (EdgeObj 𝓜)` and a vertex `w`, the number of colours whose
matching misses `w` is at most the number of missing degrees of `w` plus the
number of edge objects through `w` used by no colour. -/
theorem objCover {n D : ℕ} {𝓜 : MultiHypergraph n}
    (N : Fin D → Set (EdgeObj 𝓜)) (hmatch : ∀ i, IsObjMatching (N i)) (w : Fin n) :
    (({c : Fin D | w ∉ objVert (N c)} : Set (Fin D)).ncard : ℝ) ≤
      ((D : ℝ) - (𝓜.deg w : ℝ))
        + (({x ∈ objThrough 𝓜 w | ∀ c : Fin D, x ∉ N c}).ncard : ℝ) := by
  classical
  haveI : Finite (EdgeObj 𝓜) := finite_edgeObj 𝓜
  have hunivfin : (Set.univ : Set (EdgeObj 𝓜)).Finite := Set.finite_univ
  -- the notation of the module header
  set T : Set (EdgeObj 𝓜) := objThrough 𝓜 w with hT
  set B : Set (EdgeObj 𝓜) := {x ∈ T | ∀ c : Fin D, x ∉ N c} with hB
  set Used : Set (EdgeObj 𝓜) := {x ∈ T | ∃ c : Fin D, x ∈ N c} with hUsed
  set Cov : Set (Fin D) := {c | w ∈ objVert (N c)} with hCov
  set A : Set (Fin D) := {c | w ∉ objVert (N c)} with hA
  have hTfin : T.Finite := hunivfin.subset (Set.subset_univ _)
  have hBfin : B.Finite := hTfin.subset (fun x hx => hx.1)
  have hUsedfin : Used.Finite := hTfin.subset (fun x hx => hx.1)
  have hCovfin : Cov.Finite := Set.finite_univ.subset (Set.subset_univ _)
  have hAfin : A.Finite := Set.finite_univ.subset (Set.subset_univ _)
  -- `T` has `𝓜.deg w` elements
  have hTdeg : T.ncard = 𝓜.deg w := by rw [hT]; exact objThrough_ncard 𝓜 w
  -- (a) `A` and `Cov` partition `Fin D`, so `|A| = D - |Cov|`
  have hAcov : A ∪ Cov = (Set.univ : Set (Fin D)) := by
    ext c
    constructor
    · intro _; exact Set.mem_univ c
    · intro _
      by_cases h : w ∈ objVert (N c)
      · exact Or.inr (by simpa [hCov] using h)
      · exact Or.inl (by simpa [hA] using h)
  have hdisjAC : Disjoint A Cov := by
    refine Set.disjoint_left.mpr fun c hcA hcC => ?_
    rw [hA] at hcA
    rw [hCov] at hcC
    exact hcA hcC
  have hcardA : A.ncard + Cov.ncard = D := by
    have h1 := Set.ncard_union_eq hdisjAC hAfin hCovfin
    rw [hAcov, Set.ncard_univ, Nat.card_fin] at h1
    exact h1.symm
  -- (b) `B` and `Used` partition `T`, so `|B| + |Used| = 𝓜.deg w`
  have hBU : B ∪ Used = T := by
    ext x
    constructor
    · rintro (h | h)
      · rw [hB] at h; exact h.1
      · rw [hUsed] at h; exact h.1
    · intro hx
      by_cases h : ∃ c : Fin D, x ∈ N c
      · exact Or.inr (by rw [hUsed]; exact ⟨hx, h⟩)
      · exact Or.inl (by rw [hB]; exact ⟨hx, fun c hc => h ⟨c, hc⟩⟩)
  have hdisjBU : Disjoint B Used := by
    refine Set.disjoint_left.mpr fun x hxB hxU => ?_
    rw [hB] at hxB
    rw [hUsed] at hxU
    obtain ⟨c, hc⟩ := hxU.2
    exact hxB.2 c hc
  have hcardT : B.ncard + Used.ncard = 𝓜.deg w := by
    have h1 := Set.ncard_union_eq hdisjBU hBfin hUsedfin
    rw [hBU] at h1
    exact h1.symm.trans hTdeg
  -- (c) each colour uses at most one object through `w`, hence `|Used| ≤ |Cov|`
  set P : Set (EdgeObj 𝓜 × Fin D) := {p | p.1 ∈ N p.2 ∧ w ∈ EdgeObj.toSet p.1} with hP
  have hPfin : P.Finite := by
    have h : (T ×ˢ (Set.univ : Set (Fin D))).Finite := hTfin.prod Set.finite_univ
    refine h.subset ?_
    rintro ⟨x, c⟩ hp
    rw [hP] at hp
    exact ⟨by rw [hT]; simpa [objThrough] using hp.2, Set.mem_univ c⟩
  -- `fst` maps `P` onto `Used`
  have hfst : Prod.fst '' P = Used := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [hP] at hp
      rw [hUsed]
      exact ⟨by rw [hT]; simpa [objThrough] using hp.2, ⟨p.2, hp.1⟩⟩
    · intro hx
      rw [hUsed] at hx
      obtain ⟨hxT, c, hxc⟩ := hx
      refine ⟨(x, c), ?_, rfl⟩
      rw [hP]
      exact ⟨hxc, by rw [hT] at hxT; simpa [objThrough] using hxT⟩
  -- `snd` is injective on `P`: two objects of one matching through `w` coincide
  have hinj : Set.InjOn Prod.snd P := by
    rintro ⟨x, c⟩ hp ⟨y, d⟩ hq heq
    rw [hP] at hp hq
    have hcd : c = d := heq
    have hx : x = y := by
      by_contra hne
      have hdisj : Disjoint (EdgeObj.toSet x) (EdgeObj.toSet y) :=
        hmatch c x hp.1 y (by rw [hcd]; exact hq.1) hne
      exact (Set.disjoint_left.mp hdisj hp.2) hq.2
    rw [Prod.ext_iff]
    exact ⟨hx, hcd⟩
  -- `snd '' P` consists of covering colours
  have hsnd : Prod.snd '' P ⊆ Cov := by
    rintro c ⟨p, hp, rfl⟩
    rw [hP] at hp
    rw [hCov]
    exact mem_objVert.mpr ⟨p.1, hp.1, hp.2⟩
  have hcrux : Used.ncard ≤ Cov.ncard := by
    calc Used.ncard = (Prod.fst '' P).ncard := by rw [hfst]
      _ ≤ P.ncard := Set.ncard_image_le hPfin
      _ = (Prod.snd '' P).ncard := hinj.ncard_image.symm
      _ ≤ Cov.ncard := Set.ncard_le_ncard hsnd hCovfin
  -- assemble in `ℝ`
  have hA' : ((A.ncard : ℕ) : ℝ) + ((Cov.ncard : ℕ) : ℝ) = (D : ℝ) := by exact_mod_cast hcardA
  have hT' : ((B.ncard : ℕ) : ℝ) + ((Used.ncard : ℕ) : ℝ) = ((𝓜.deg w : ℕ) : ℝ) := by
    exact_mod_cast hcardT
  have hU' : ((Used.ncard : ℕ) : ℝ) ≤ ((Cov.ncard : ℕ) : ℝ) := by exact_mod_cast hcrux
  linarith

end Work.Deep.Nibble
