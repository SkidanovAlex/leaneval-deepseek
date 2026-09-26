import Mathlib
import Submission.Work.SG.EdgeSetDefs
import Submission.Work.SG.sb_permMat

/-!
### The undirected edge set of `suppGraph Q (W * permMat τ)`

Relabelling the superbase of `W` by a permutation `τ` (i.e. passing to `W * permMat τ`,
see `sb_permMat`) acts on the underlying *undirected* edge set of the support graph by
`τ⁻¹ = τ.symm`:

`edgeSet (suppGraph Q (W * permMat τ)) = (edgeSet (suppGraph Q W)).image (Sym2.map τ.symm)`.

Symmetry of `Q` is needed: only then is the defining condition of an edge
`bf Q (sb W a) (sb W b) < 0` symmetric in `a`, `b` (`bf_comm`), so that the support graph may be
read as a graph on unordered pairs `Sym2 (Fin 4)` via `Sym2.fromRel`.

The proof introduces the symmetric relation `suppEdgeRel Q W` on superbase indices
(`a ≠ b` and a negative cross term), shows that `edgeSet (suppGraph Q W)` is exactly
`Sym2.fromRel` of it (`edgeSet_suppGraph_eq_fromRel`), and concludes with the functoriality of
`Sym2.fromRel` under `Sym2.map` (`Sym2.fromRel_relationMap`).
-/

namespace Work.SG

/-- The relation on superbase indices underlying the support graph of an obtuse superbase **and**
symmetry of `Q`: `a ≠ b` and a strictly negative cross term `bf Q (sb W a) (sb W b) < 0`. -/
def suppEdgeRel (Q W : IMat) (a b : Fin 4) : Prop :=
  a ≠ b ∧ bf Q (sb W a) (sb W b) < 0

/-- For symmetric `Q` the relation `suppEdgeRel Q W` is symmetric: this is exactly where
symmetry of `Q` is used (`bf_comm`). -/
theorem suppEdgeRel_symm (Q W : IMat) (hsym : Q.transpose = Q) : Std.Symm (suppEdgeRel Q W) where
  symm a b h := ⟨h.1.symm, by rw [bf_comm Q hsym]; exact h.2⟩

/-- Membership of the unordered pair `{a,b}` in the edge set of the support graph: it is an edge
iff `a ≠ b` and the cross term is strictly negative, in *either* order of `a`, `b`. -/
theorem mem_edgeSet_suppGraph (Q W : IMat) (hsym : Q.transpose = Q) (a b : Fin 4) :
    s(a, b) ∈ edgeSet (suppGraph Q W) ↔ suppEdgeRel Q W a b := by
  constructor
  · intro h
    rw [mem_edgeSet] at h
    obtain ⟨p, hp, hsp⟩ := h
    rw [mem_suppGraph] at hp
    obtain ⟨hlt, hbf⟩ := hp
    have hne : p.1 ≠ p.2 := ne_of_lt hlt
    rw [Sym2.eq_iff] at hsp
    rcases hsp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hne, hbf⟩
    · refine ⟨hne.symm, ?_⟩
      rw [bf_comm Q hsym]
      exact hbf
  · rintro ⟨hne, hbf⟩
    rw [mem_edgeSet]
    refine ⟨nrmEdge a b, ?_, nrmEdge_sym2 a b⟩
    rw [mem_suppGraph]
    refine ⟨nrmEdge_fst_lt a b hne, ?_⟩
    rcases nrmEdge_eq a b with h | h <;> rw [h]
    · exact hbf
    · rw [bf_comm Q hsym]; exact hbf

/-- The edge set of the support graph is the `Sym2.fromRel` set of `suppEdgeRel`. -/
theorem edgeSet_suppGraph_eq_fromRel (Q W : IMat) (hsym : Q.transpose = Q) :
    (edgeSet (suppGraph Q W) : Set (Sym2 (Fin 4))) =
      Sym2.fromRel (suppEdgeRel_symm Q W hsym) := by
  ext z
  refine Sym2.ind (fun a b => ?_) z
  rw [Sym2.fromRel_prop, Finset.mem_coe]
  exact mem_edgeSet_suppGraph Q W hsym a b

theorem edgeSet_suppGraph_mul_permMat {Q W : IMat} {τ : Equiv.Perm (Fin 4)}
    (hsym : Q.transpose = Q) :
    edgeSet (suppGraph Q (W * permMat τ)) =
      (edgeSet (suppGraph Q W)).image (Sym2.map τ.symm) := by
  apply Finset.coe_injective
  rw [Finset.coe_image, edgeSet_suppGraph_eq_fromRel Q W hsym,
      edgeSet_suppGraph_eq_fromRel Q (W * permMat τ) hsym]
  rw [← Sym2.fromRel_relationMap (suppEdgeRel_symm Q W hsym) τ.symm]
  ext z
  refine Sym2.ind (fun a b => ?_) z
  rw [Sym2.fromRel_prop, Sym2.fromRel_prop, Relation.map_apply]
  unfold suppEdgeRel
  simp only [sb_permMat]
  constructor
  · rintro ⟨hne, hbf⟩
    exact ⟨τ a, τ b, ⟨fun h => hne (τ.injective h), hbf⟩, by simp, by simp⟩
  · rintro ⟨x, y, ⟨hxy, hbf⟩, hx, hy⟩
    have hx' : x = τ a := by rw [← hx]; simp
    have hy' : y = τ b := by rw [← hy]; simp
    subst hx'; subst hy'
    exact ⟨fun h => hxy (congrArg τ h), hbf⟩

end Work.SG
