import Mathlib
import Submission.Work.ThomBordism.genuineTubeData
import Submission.Work.ThomBordism.nonempty_genuineTubeData
import Submission.Work.ThomBordism.tubeConnForm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The genuine tubular data of a finite family

`Work.ThomBordism.nonempty_genuineTubeData` produces the TUBULAR half of the genuine collapse data of
**one** embedded piece at a prescribed odd codimension.  The collar producer of the last mile consumes
the whole family at once (`Work.PTGeometric.ConcreteLastMileSource` quantifies over
`G : GenuineTubeGeometry k D ι Fam`), with *one* codimension `k` for all pieces, chosen odd and above
the family's embedding bound.  This file is that lift: the family form of the genuine tube data, with
the common codimension and the embeddings as explicit witnesses (the collar producer reads them).

It is the exact interface between `Work.ThomBordism.familyTubeRep` /
`Work.ThomBordism.nonempty_genuineTubeData` (the TUBULAR half) and
`Work.PTGeometric.GenuineTubeGeometry` (whose remaining fields are the coordinate half of the concrete
Thom space, area PTGEOMETRIC's).
-/

namespace Work.ThomBordism

noncomputable section

open Work.ThomBordism.PontryaginThom

/-- **The genuine tubular data of a finite family of connected closed oriented `8`-manifolds**, at a
common odd codimension `k ≥ 11` above the family's embedding bound.  The codimension is chosen by the
producer (it is existential, as in the collar producer's hypothesis), the embeddings at that
codimension are exposed as a witness, and the comparison map of the universal target is the canonical
`Φ := PhiG k`. -/
theorem nonempty_genuineTubeData_family {ι : Type} [Fintype ι] (F : ι → Man8)
    (hconn : ∀ i, ConnectedSpace (F i).pt) (N : ∀ i, NormalBundlData (F i)) :
    ∃ (k : ℕ) (_ : 11 ≤ k) (_ : Odd k)
      (_emb : ∀ i, Nonempty (EmbeddingData (F i) (8 + k))),
      Nonempty (∀ i, GenuineTubeData (F i) k
        (connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))) (N i)) := by
  obtain ⟨k, hk, hodd, hE⟩ := exists_embeddingData_ge_family_odd' F
  refine ⟨k, hk, hodd, hE, ?_⟩
  refine ⟨fun i => Classical.choice (nonempty_genuineTubeData (V := F i) (k := k) hk hodd
    (Classical.choice (hE i)) (N i))⟩

/-- **The same at a *prescribed* odd codimension** (the form the collar producer uses when it has
already fixed `k`): if every member embeds in `ℝ^{8+k}` for an odd `k ≥ 11`, the genuine tubular data
of the whole family exist at that `k`. -/
theorem nonempty_genuineTubeData_family_at {k : ℕ} (hk : 11 ≤ k) (hodd : Odd k)
    {ι : Type} [Fintype ι] (F : ι → Man8) (hconn : ∀ i, ConnectedSpace (F i).pt)
    (hE : ∀ i, Nonempty (EmbeddingData (F i) (8 + k)))
    (N : ∀ i, NormalBundlData (F i)) :
    Nonempty (∀ i, GenuineTubeData (F i) k
      (connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))) (N i)) :=
  ⟨fun i => Classical.choice (nonempty_genuineTubeData (V := F i) (k := k) hk hodd
    (Classical.choice (hE i)) (N i))⟩

end

end Work.ThomBordism
