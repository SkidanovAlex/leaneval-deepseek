import Mathlib
import Submission.Work.CORE2B.L29Parts
import Submission.Work.CORE2B.L29CallSite
import Submission.Work.CORE2B.API

namespace Work.CORE2B

open Subgroup

-- Leaf P3 of the lead's design pass 15 (Lemma 2.9): conjugation transport of a witness pair.
-- Conjugating by `g ∈ N_G(V)` with `g u g⁻¹ = t` moves a witness pair `(u, v)` for `A` to the
-- witness pair `(t, g v g⁻¹)` for `A^g = Work.GW2.conjSub g A`, preserving nilpotency, odd order,
-- `V ≤ N(A)` and faithfulness.
--
-- Everything below is pure conjugation bookkeeping: `conjSub g A = A^g = gAg⁻¹` is the image of `A`
-- under the automorphism `MulAut.conj g : x ↦ g x g⁻¹`, and each of the six conjuncts is transported
-- along that automorphism.  The hypothesis `g ∈ N_G(V)` is what makes `V` itself invariant, so that
-- `V ≤ N(A)` and faithfulness can be transported to `A^g` (note `g` need not normalize `A`).

/-- The centralizer of `u` conjugated by `g` is the centralizer of `g u g⁻¹`, and conjugation
distributes over the intersection with `A`: `(A ⊓ C(u))^g = A^g ⊓ C(u^g)`.

This is the exact-form version of `Subgroup.map_inf` plus the (injective) transport of point
centralizers; it is what turns the commutator `⁅⟨v⟩, A ⊓ C_A(u)⁆` into `⁅⟨v^g⟩, A^g ⊓ C(t)⁆`. -/
theorem conjSub_map_inf_centralizer {G : Type} [Group G] (A : Subgroup G) (u g : G) :
    (A ⊓ Subgroup.centralizer ({u} : Set G)).map (MulAut.conj g).toMonoidHom
      = A.map (MulAut.conj g).toMonoidHom ⊓
        Subgroup.centralizer ({(MulAut.conj g) u} : Set G) := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨haA, hau⟩ := ha
    refine ⟨Subgroup.mem_map_of_mem _ haA, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have hau' : u * a = a * u := Subgroup.mem_centralizer_iff.mp hau u (by simp)
    show (MulAut.conj g) u * (MulAut.conj g) a = (MulAut.conj g) a * (MulAut.conj g) u
    rw [← MulEquiv.map_mul, ← MulEquiv.map_mul, hau']
  · intro hx
    obtain ⟨hxA, hxC⟩ := hx
    obtain ⟨a, haA, rfl⟩ := Subgroup.mem_map.mp hxA
    refine Subgroup.mem_map_of_mem _ ⟨haA, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have hcomm : (MulAut.conj g) u * (MulAut.conj g) a
        = (MulAut.conj g) a * (MulAut.conj g) u :=
      Subgroup.mem_centralizer_iff.mp hxC ((MulAut.conj g) u) (by simp)
    show u * a = a * u
    have h2 := congrArg (fun z => (MulAut.conj g)⁻¹ z) hcomm
    simpa using h2

/-- Conjugation transport of the commutator witnessing that `v` does not commute with all of
`A ⊓ C(u)`: if `g u g⁻¹ = t` then
`⁅⟨v^g⟩, A^g ⊓ C(t)⁆ = (⁅⟨v⟩, A ⊓ C(u)⁆)^g`, the image of the original commutator under the
automorphism `conj g`. -/
theorem conjSub_commutator_transport {G : Type} [Group G] (A : Subgroup G) (u v g t : G)
    (hgut : g * u * g⁻¹ = t) :
    (⁅Subgroup.zpowers v, A ⊓ Subgroup.centralizer ({u} : Set G)⁆).map
        (MulAut.conj g).toMonoidHom
      = ⁅Subgroup.zpowers (g * v * g⁻¹),
          Work.GW2.conjSub g A ⊓ Subgroup.centralizer ({t} : Set G)⁆ := by
  rw [Subgroup.map_commutator, MonoidHom.map_zpowers, conjSub_map_inf_centralizer]
  show ⁅Subgroup.zpowers ((MulAut.conj g) v),
      Work.GW2.conjSub g A ⊓ Subgroup.centralizer ({(MulAut.conj g) u} : Set G)⁆
    = ⁅Subgroup.zpowers (g * v * g⁻¹),
        Work.GW2.conjSub g A ⊓ Subgroup.centralizer ({t} : Set G)⁆
  simp only [MulAut.conj_apply, hgut]

theorem L29TransportProp_proved : Work.CORE2B.C15.L29TransportProp := by
  intro G _ _ A V u v g t hAnil hAodd hNA hFaith hu hv hgV hgut hcom
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- nilpotency transports along the isomorphism `A ≃* A^g`
    haveI := hAnil
    rw [Work.GW2.conjSub]
    exact Group.nilpotent_of_mulEquiv
      (Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
  · -- odd order transports (the cardinality is preserved by the injective map)
    have hcard : Nat.card ↥(Work.GW2.conjSub g A) = Nat.card ↥A := by
      rw [Work.GW2.conjSub]
      exact Subgroup.card_map_of_injective (MulAut.conj g).injective
    rwa [hcard]
  · -- `V ≤ N(A)` transports: `g⁻¹ v g ∈ V ⊆ N(A)` for every `v ∈ V`
    intro v hv
    have hwV : g⁻¹ * v * g ∈ V := (Subgroup.mem_set_normalizer_iff''.mp hgV v).mp hv
    have hwN : g⁻¹ * v * g ∈ normalizer (A : Set G) := hNA hwV
    have hw1 : ∀ a : G, a ∈ A ↔ (g⁻¹ * v * g) * a * (g⁻¹ * v * g)⁻¹ ∈ A :=
      Subgroup.mem_set_normalizer_iff.mp hwN
    have hw2 : ∀ a : G, a ∈ A ↔ (g⁻¹ * v * g)⁻¹ * a * (g⁻¹ * v * g) ∈ A :=
      Subgroup.mem_set_normalizer_iff''.mp hwN
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [Work.GW2.conjSub] at hh
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hh
      rw [Work.GW2.conjSub]
      refine Subgroup.mem_map.mpr
        ⟨(g⁻¹ * v * g) * a * (g⁻¹ * v * g)⁻¹, (hw1 a).mp ha, ?_⟩
      show (MulAut.conj g) ((g⁻¹ * v * g) * a * (g⁻¹ * v * g)⁻¹) = v * (MulAut.conj g) a * v⁻¹
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    · intro hh
      rw [Work.GW2.conjSub] at hh
      obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hh
      rw [Work.GW2.conjSub]
      refine Subgroup.mem_map.mpr
        ⟨(g⁻¹ * v * g)⁻¹ * a * (g⁻¹ * v * g), (hw2 a).mp ha, ?_⟩
      have haeq' : (MulAut.conj g) a = v * h * v⁻¹ := haeq
      have hval : h = v⁻¹ * ((MulAut.conj g) a) * v := by
        rw [haeq']; group
      rw [hval]
      show (MulAut.conj g) ((g⁻¹ * v * g)⁻¹ * a * (g⁻¹ * v * g))
        = v⁻¹ * (MulAut.conj g) a * v
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
  · -- faithfulness transports: conjugate back by `g⁻¹`
    intro v hv hv1 hle
    have hwV : g⁻¹ * v * g ∈ V := (Subgroup.mem_set_normalizer_iff''.mp hgV v).mp hv
    have hw1 : g⁻¹ * v * g ≠ 1 := by
      intro h
      refine hv1 ?_
      calc v = g * (g⁻¹ * v * g) * g⁻¹ := by group
        _ = g * 1 * g⁻¹ := by rw [h]
        _ = 1 := by group
    refine hFaith (g⁻¹ * v * g) hwV hw1 ?_
    intro a ha
    have hmem : (MulAut.conj g).toMonoidHom a ∈ Work.GW2.conjSub g A :=
      Subgroup.mem_map_of_mem _ ha
    have hcomm : v * ((MulAut.conj g) a) = ((MulAut.conj g) a) * v :=
      Subgroup.mem_centralizer_iff.mp (hle hmem) v (by simp)
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    show (g⁻¹ * v * g) * a = a * (g⁻¹ * v * g)
    have h3 : g⁻¹ * (v * (g * a * g⁻¹)) * g = g⁻¹ * ((g * a * g⁻¹) * v) * g :=
      congrArg (fun z => g⁻¹ * z * g) hcomm
    have e1 : (g⁻¹ * v * g) * a = g⁻¹ * (v * (g * a * g⁻¹)) * g := by group
    have e2 : a * (g⁻¹ * v * g) = g⁻¹ * ((g * a * g⁻¹) * v) * g := by group
    rw [e1, e2]
    exact h3
  · -- `g v g⁻¹ ∈ V` since `g ∈ N_G(V)`
    exact (Subgroup.mem_set_normalizer_iff.mp hgV v).mp hv
  · -- the witness commutes back to non-triviality
    have h1 := conjSub_commutator_transport A u v g t hgut
    intro hbot
    have h2 : (⁅Subgroup.zpowers v, A ⊓ Subgroup.centralizer ({u} : Set G)⁆).map
        (MulAut.conj g).toMonoidHom = ⊥ := by rw [h1, hbot]
    exact hcom ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp h2)

end Work.CORE2B
