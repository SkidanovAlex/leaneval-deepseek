import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Coprime transitive actions: the stabilizer is transitive on the other set

Let a finite group `G` act transitively on two finite sets `A` and `B`, with
`Nat.card A` and `Nat.card B` coprime.  Then the stabilizer `H ≤ G` of a point `a : A`
acts transitively on `B`: for all `b b' : B` there is `g ∈ G` with `g • a = a` and
`g • b = b'`.

This is the classical "coprime orbit" lemma (a special case of the fact that if
`H, K ≤ G` and `[G : H]`, `[G : K]` are coprime then `G = H · K`), and it is exactly
the statement needed by Wagner's proposition: a doubly transitive group acting on the
nonzero vectors of an `𝔽₂`-space has a point stabilizer that is transitive on the
complement.

The proof is a pure counting argument.  Put `H := stabilizer G a`, `K := stabilizer G b`.
The two-step chain
`(H ⊓ K).relIndex H * H.index = (H ⊓ K).index = (H ⊓ K).relIndex K * K.index`
combined with `H.index = Nat.card A`, `K.index = Nat.card B` gives
`[H : H ⊓ K] * Nat.card A = [K : H ⊓ K] * Nat.card B`.
Since `Nat.card A` and `Nat.card B` are coprime, `Nat.card B ∣ [H : H ⊓ K]`.
But `[H : H ⊓ K]` is the cardinality of the `H`-orbit of `b`, which is at most
`Nat.card B`; hence it equals `Nat.card B` and the orbit is everything.
-/

namespace Work.Hering.Wagner

theorem exists_smul_eq_of_smul_eq_of_coprime {G A B : Type*} [Group G] [MulAction G A] [MulAction G B]
    [Finite G] [Finite A] [Finite B] (hA : ∀ a a' : A, ∃ g : G, g • a = a')
    (hB : ∀ b b' : B, ∃ g : G, g • b = b') (a : A)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card B)) :
    ∀ b b' : B, ∃ g : G, g • a = a ∧ g • b = b' := by
  intro b b'
  let H : Subgroup G := MulAction.stabilizer G a
  let K : Subgroup G := MulAction.stabilizer G b
  have horbA : MulAction.orbit G a = Set.univ :=
    Set.eq_univ_of_forall fun x => MulAction.mem_orbit_iff.mpr (hA a x)
  have horbB : MulAction.orbit G b = Set.univ :=
    Set.eq_univ_of_forall fun x => MulAction.mem_orbit_iff.mpr (hB b x)
  have hHidx : H.index = Nat.card A := by
    show (MulAction.stabilizer G a).index = Nat.card A
    rw [MulAction.index_stabilizer, horbA, Set.ncard_univ]
  have hKidx : K.index = Nat.card B := by
    show (MulAction.stabilizer G b).index = Nat.card B
    rw [MulAction.index_stabilizer, horbB, Set.ncard_univ]
  have hkey : (H ⊓ K).relIndex H * Nat.card A = (H ⊓ K).relIndex K * Nat.card B := by
    rw [← hHidx, ← hKidx]
    exact (Subgroup.relIndex_mul_index (inf_le_left : H ⊓ K ≤ H)).trans
      (Subgroup.relIndex_mul_index (inf_le_right : H ⊓ K ≤ K)).symm
  have hdiv : Nat.card B ∣ (H ⊓ K).relIndex H * Nat.card A := by
    rw [hkey]; exact dvd_mul_left (Nat.card B) _
  have hBdvd : Nat.card B ∣ (H ⊓ K).relIndex H := hcop.symm.dvd_of_dvd_mul_right hdiv
  have hrelH : (H ⊓ K).relIndex H = (MulAction.orbit H b).ncard := by
    show ((H ⊓ K).subgroupOf H).index = _
    have hstab : (H ⊓ K).subgroupOf H = MulAction.stabilizer H b := by
      ext x
      simp only [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.smul_def,
        Subgroup.mem_inf]
      constructor
      · intro hx; exact MulAction.mem_stabilizer_iff.mp hx.2
      · intro hx; exact ⟨x.2, MulAction.mem_stabilizer_iff.mpr hx⟩
    rw [hstab, MulAction.index_stabilizer]
  have hBdvd' : Nat.card B ∣ (MulAction.orbit H b).ncard := by rw [← hrelH]; exact hBdvd
  have hle : (MulAction.orbit H b).ncard ≤ Nat.card B := by
    rw [← Set.ncard_univ B]
    exact Set.ncard_le_ncard (Set.subset_univ _)
  have hpos : 0 < (MulAction.orbit H b).ncard :=
    (Set.ncard_pos (s := MulAction.orbit H b)).mpr ⟨b, MulAction.mem_orbit_self b⟩
  have hge : Nat.card B ≤ (MulAction.orbit H b).ncard := Nat.le_of_dvd hpos hBdvd'
  have horbit : MulAction.orbit H b = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by rw [Set.ncard_univ]; exact hge)
  have hb'mem : b' ∈ MulAction.orbit H b := by rw [horbit]; exact Set.mem_univ b'
  obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.mp hb'mem
  refine ⟨(x : G), ?_, ?_⟩
  · exact MulAction.mem_stabilizer_iff.mp x.2
  · rw [Subgroup.smul_def] at hx; exact hx

end Work.Hering.Wagner
