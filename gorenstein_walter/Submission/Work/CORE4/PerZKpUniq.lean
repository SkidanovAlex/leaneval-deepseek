import Mathlib
import Submission.Work.CORE4.Defs27
import Submission.Work.CORE4.BadCountInH
import Submission.Work.CORE4.L2TorusNormE
import Submission.Work.CORE4.ConjSub.conjSub_mul

namespace Work.CORE4

/-! ## Conjugation helpers

`Work.GW2.conjSub c K = c K c⁻¹ = K.map (MulAut.conj c).toMonoidHom`.  The four little facts
below are the ones the proof of `PerZKpUniq` transports along `c`; they are proved here so that
the file is self-contained.
-/

/-- `conjSub 1 K = K`. -/
lemma conjSub_one_c4 {G : Type} [Group G] (K : Subgroup G) :
    Work.GW2.conjSub 1 K = K := by
  ext x
  rw [Work.CORE4.ConjSub.mem_conjSub]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa using hk
  · intro hx
    exact ⟨x, hx, by simp⟩

/-- The conjugation action on subgroups is invertible: `(K^{c⁻¹})^c = K`. -/
lemma conjSub_conjSub_inv_c4 {G : Type} [Group G] (c : G) (K : Subgroup G) :
    Work.GW2.conjSub c (Work.GW2.conjSub c⁻¹ K) = K := by
  rw [← Work.CORE4.ConjSub.conjSub_mul c c⁻¹ K, mul_inv_cancel, conjSub_one_c4]

/-- Conjugation preserves the cardinality of a subgroup. -/
lemma card_conjSub_c4 {G : Type} [Group G] (c : G) (K : Subgroup G) :
    Nat.card ↥(Work.GW2.conjSub c K) = Nat.card ↥K := by
  rw [Work.GW2.conjSub]
  exact Subgroup.card_map_of_injective (MulAut.conj c).injective

/-- The centralizer of a conjugate subgroup is the conjugate of the centralizer. -/
lemma centralizer_conjSub_c4 {G : Type} [Group G] (c : G) (K : Subgroup G) :
    Subgroup.centralizer ((Work.GW2.conjSub c K : Subgroup G) : Set G) =
      Subgroup.map (MulAut.conj c).toMonoidHom (Subgroup.centralizer (K : Set G)) :=
  (Work.CORE4.TorusTransport.map_centralizer_eq_centralizer_map (MulAut.conj c) K).symm

/-- Centralizing a conjugate subgroup is transported by `c⁻¹`: if `Z ≤ C_G(K^c)` then
`Z^{c⁻¹} ≤ C_G(K)`. -/
lemma conjSub_inv_le_centralizer_c4 {G : Type} [Group G] (c : G) {K Z : Subgroup G}
    (h : Z ≤ Subgroup.centralizer (Work.GW2.conjSub c K : Set G)) :
    Work.GW2.conjSub c⁻¹ Z ≤ Subgroup.centralizer (K : Set G) := by
  have h1 : Subgroup.map (MulAut.conj c⁻¹).toMonoidHom Z ≤
      Subgroup.map (MulAut.conj c⁻¹).toMonoidHom
        (Subgroup.centralizer ((Work.GW2.conjSub c K : Subgroup G) : Set G)) :=
    Subgroup.map_mono h
  rw [centralizer_conjSub_c4 c K, Subgroup.map_map] at h1
  refine h1.trans (le_of_eq ?_)
  have hcomp : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  rw [hcomp, Subgroup.map_id]

/-- **Uniqueness of the order-`p` subgroup of the layer centralizing `Kp`.**

In the §4 configuration, let `E = layerIn h.D.M ≅ L₂(q)` (§4 (9)), let `P ≤ h.D.F` have prime
order `p` with associated `(p,p)`-subgroup `A` of §4 (8), and let `Kp ≤ h.D.K` have order `p`.
If `Z ≤ E^c` has order `p` and centralizes `Kp^c`, then `Z = Kp^c`.

Indeed `Kp ≤ E` (`K_le_layerIn`), the prime `p` is odd and `≠ nineP h` (`p_parity_facts`, from
`p ∣ |K| ∣ k` and `2k = q ± 1`), so `C_E(Kp)` is a torus of `E ≅ L₂(q)`, hence cyclic
(`L2TorusNormE`).  Transporting along `c` (`conjSub_inv_le_centralizer_c4`) puts `Z^{c⁻¹}` in
`C_E(Kp)`; both `Z^{c⁻¹}` and `Kp` are order-`p` subgroups of the cyclic `C_E(Kp)`, so they
coincide (`eq_Kp_of_le_centralizer_Kp`), and conjugating back gives `Z = Kp^c`. -/
theorem PerZKpUniq (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) (p : ℕ) (P A : Subgroup G)
        (Kp : Subgroup G) (c : G) (Z : Subgroup G),
        p.Prime → P ≤ h.D.F → Nat.card ↥P = p → Work.GW2.Case2EightObj h.D p P A →
        Kp ≤ h.D.K → Nat.card ↥Kp = p →
        Z ≤ Work.GW2.conjSub c (Work.GW2.layerIn h.D.M) → Nat.card ↥Z = p →
        Z ≤ Subgroup.centralizer (Work.GW2.conjSub c Kp : Set G) →
        Z = Work.GW2.conjSub c Kp := by
  intro G _ _ hbc B h p P A Kp c Z hp hPF hPcard hObj hKpK hKpcard hZle hZcard hZcent
  -- `p` is odd and `p ≠ nineP h`, so the `L₂(q)` torus input applies to `Kp`
  have hpar : Odd p ∧ p ≠ 2 ∧ p ≠ Work.CORE4.nineP h :=
    Work.CORE4.p_parity_facts I hbc h hp hPF hPcard hObj
  -- `Z^{c⁻¹}` lies in the layer, has order `p`, and centralizes `Kp`
  have hTle : Work.GW2.conjSub c⁻¹ Z ≤ Work.GW2.layerIn h.D.M := by
    have h1 : Work.GW2.conjSub c⁻¹ Z ≤
        Work.GW2.conjSub c⁻¹ (Work.GW2.conjSub c (Work.GW2.layerIn h.D.M)) :=
      Subgroup.map_mono hZle
    rwa [← Work.CORE4.ConjSub.conjSub_mul c⁻¹ c (Work.GW2.layerIn h.D.M), inv_mul_cancel,
      conjSub_one_c4] at h1
  have hTcard : Nat.card ↥(Work.GW2.conjSub c⁻¹ Z) = p := by
    rw [card_conjSub_c4]
    exact hZcard
  have hTcent : Work.GW2.conjSub c⁻¹ Z ≤ Subgroup.centralizer (Kp : Set G) :=
    conjSub_inv_le_centralizer_c4 c hZcent
  have hTKp : Work.GW2.conjSub c⁻¹ Z = Kp :=
    Work.CORE4.eq_Kp_of_le_centralizer_Kp I hbc h hp hpar hKpK hKpcard hTle hTcard hTcent
  rw [← hTKp]
  exact (conjSub_conjSub_inv_c4 c Z).symm

end Work.CORE4
