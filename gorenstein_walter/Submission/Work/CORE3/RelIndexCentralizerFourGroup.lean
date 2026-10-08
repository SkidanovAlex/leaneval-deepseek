import Mathlib
import Submission.Work.CORE3.Defs

set_option linter.style.haveILetI false

namespace Work.CORE3

-- (put this in `namespace Work.CORE3`, so the full name is `Work.CORE3.RelIndexCentralizerFourGroup`)
/-- Bender 1981 §3: for a four-group `V ≤ G` on whose three involutions a subgroup `K ≤ N_G(V)`
acts transitively by conjugation, the stabiliser of a point is a subgroup of index `3`:
`|K : C_K(v)| = 3`.  (Used with `K = Ĥ`, `V = O₂(Ĥ)`, `v = t`: `[Ĥ : C_G(t)] = 3`.)  Proof:
the conjugation orbit of `v` is exactly `V ∖ {1}` (contained in `V` because `K ≤ N_G(V)`, all of
`V^#` by transitivity), so orbit-stabiliser gives `|K| = 3 · |C_K(v)|`. -/
theorem RelIndexCentralizerFourGroup {G : Type} [Group G] [Finite G]
    (V K : Subgroup G) (hV : Work.GW2.IsFourGroup V)
    (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (htrans : ∀ x ∈ V, ∀ y ∈ V, x ≠ 1 → y ≠ 1 → ∃ g ∈ K, g * x * g⁻¹ = y)
    {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    (Subgroup.centralizer ({v} : Set G) ⊓ K).relIndex K = 3 := by
  classical
  -- `K` acts on `G` by conjugation.
  letI : MulAction K G := MulAction.compHom G (MulAut.conj.comp K.subtype)
  -- The stabiliser of `v` for this action is `C_G(v) ∩ K`.
  have hstab : MulAction.stabilizer K v
      = (Subgroup.centralizer ({v} : Set G) ⊓ K).subgroupOf K := by
    ext k
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨?_, k.2⟩
      have h2 : MulAut.conj (k : G) v = v := h
      rw [MulAut.conj_apply] at h2
      rwa [mul_inv_eq_iff_eq_mul] at h2
    · rintro ⟨h1, _⟩
      change MulAut.conj (k : G) v = v
      rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
      exact h1
  -- The conjugation orbit of `v` is exactly `V ∖ {1}`.
  have horbit : MulAction.orbit K v = {x : G | x ∈ V ∧ x ≠ 1} := by
    ext x
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨k, hk⟩
      have hkx : (k : G) * v * (k : G)⁻¹ = x := by
        rw [← hk]; rfl
      refine ⟨?_, ?_⟩
      · rw [← hkx]
        exact (Subgroup.mem_normalizer_iff.mp (hKV k.2) v).mp hv
      · rintro hx1
        apply hv1
        rw [← hkx] at hx1
        have : v = (k : G)⁻¹ * 1 * (k : G) := by rw [← hx1]; group
        simpa using this
    · rintro ⟨hxV, hx1⟩
      obtain ⟨g, hgK, hgv⟩ := htrans v hv x hxV hv1 hx1
      exact ⟨⟨g, hgK⟩, by change (g : G) * v * (g : G)⁻¹ = x; exact hgv⟩
  -- `V` has four elements, so `V ∖ {1}` has three.
  have hVncard : (V : Set G).ncard = 4 := (Nat.card_coe_set_eq (V : Set G)).symm.trans hV.1
  rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer, horbit]
  rw [show ({x : G | x ∈ V ∧ x ≠ 1} : Set G) = (V : Set G) \ {1} by ext x; simp]
  rw [Set.ncard_sdiff_singleton_of_mem V.one_mem, hVncard]

end Work.CORE3
