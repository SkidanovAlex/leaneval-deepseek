import Mathlib
import Submission.Work.CORE4.Defs27
import Submission.Work.CORE4.Case2CountAssembly
import Submission.Work.CORE4.ConjSub.conjSub_mul
import Submission.Work.CORE4.Case2EHcard
import Submission.Work.CORE4.Case2PerXBound9
import Submission.Work.CORE4.Case2PerXBound9Corrected
import Submission.Work.CORE4.Case2NormalizerP
import Submission.Work.CORE4.CountSetup

namespace Work.CORE4

/-- **Facts about the members of `amalgamWit` in the per-`Z` count.**

In the `AmalgamCtx` of Bender p. 227, an element `Z = X^c` of `amalgamWit E (A ⊓ K) X q` (so
`X = P^g ≤ A = P ⊔ K_p`, `c ∈ R ≤ E(M)`, `Z ≠ X`) is again a conjugate of `P` lying inside the
copy `W = P ⊔ E(M)`; it has order `p` and it centralizes `P`.

The last fact is the one used by the per-`Z` count: `W = P ⊔ E(M)` commutes with `P`
(the `P`-part is central in `W` because `P` is abelian and the `E(M)`-part commutes with `P` by
§4 (4)), so `Z ≤ W ≤ C_G(P)`.  The fact `Z ≤ W` uses that `c ∈ E(M) ≤ M`, that `E(M) ◁ M` and
that `K_p ≤ K ≤ E(M)` (`K_le_layerIn`); `Z ≠ X` and `|Z| = |P| = p` are immediate from the
definition of `amalgamWit`. -/
theorem PerZWitFacts (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) (p : ℕ) (P A : Subgroup G)
        (Kp : Subgroup G) (g : G),
        p.Prime → P ≤ h.D.F → Nat.card ↥P = p → Work.GW2.Case2EightObj h.D p P A →
        Kp ≤ h.D.K → Nat.card ↥Kp = p → (∀ x ∈ h.D.K, x ^ p = 1 ↔ x ∈ Kp) →
        A = P ⊔ Kp → Work.GW2.conjSub g P ≤ A →
        ∀ Z ∈ Work.GW2.C27.amalgamWit (Work.GW2.layerIn h.D.M) (A ⊓ h.D.K)
            (Work.GW2.conjSub g P) (Work.CORE4.qOf h),
          Z ≠ Work.GW2.conjSub g P ∧ Z ∈ Work.CORE4.inConjSet P (Work.GW2.layerIn h.D.M) ∧
            Nat.card ↥Z = p ∧ Z ≤ Subgroup.centralizer (P : Set G) := by
  intro G _ _ hbc B h p P A Kp g hp hPF hPcard hObj hKpK hKpcard hKpomega hAeq hgle Z hZ
  simp only [Work.GW2.C27.amalgamWit, Set.mem_ofPred_eq] at hZ
  obtain ⟨hZX, R, hRE, hRcard, hRKp, c, hcR, hZeq⟩ := hZ
  -- `E(M) ◁ M`, so `c ∈ E(M) ≤ M` normalizes `E(M)`; `c ∈ M = N_G(P)` fixes `P` by conjugation.
  have hEnorm :=
    (Subgroup.normal_subgroupOf_iff (Work.CORE4.layerIn_le h.D.M)).mp
      h.layerIn_subgroupOf_normal
  have hcM : c ∈ h.D.M := (Work.CORE4.layerIn_le h.D.M) (hRE hcR)
  have hPne : P ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hPcard
    exact hp.ne_one hPcard.symm
  have hME : Subgroup.normalizer (P : Set G) = h.D.M :=
    Work.CORE4.Case2NormalizerP G B h P hPF hPne
  have hcP : Work.GW2.conjSub c P = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hME ▸ hcM)
  -- `K_p ≤ E(M)`, and `E(M)` is normal, so `K_p^c ≤ E(M)`.
  have hKpE : Kp ≤ Work.GW2.layerIn h.D.M := hKpK.trans (Work.CORE4.K_le_layerIn B h)
  have hmapKp : Work.GW2.conjSub c Kp ≤ Work.GW2.layerIn h.D.M := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := (Work.CORE4.ConjSub.mem_conjSub).mp ha
    exact hEnorm k c (hKpE hk) hcM
  -- `Z = P^(c*g) = (P^g)^c ≤ A^c = (P ⊔ K_p)^c = P ⊔ K_p^c ≤ P ⊔ E(M)`.
  have hZeq' : Z = Work.GW2.conjSub (c * g) P := by
    rw [hZeq, ← Work.CORE4.ConjSub.conjSub_mul]
  have hZE : Z ≤ P ⊔ Work.GW2.layerIn h.D.M := by
    calc Z = Work.GW2.conjSub c (Work.GW2.conjSub g P) := hZeq
      _ ≤ Work.GW2.conjSub c A := Subgroup.map_mono hgle
      _ = Work.GW2.conjSub c (P ⊔ Kp) := by rw [hAeq]
      _ = Work.GW2.conjSub c P ⊔ Work.GW2.conjSub c Kp := by
            simp only [Work.GW2.conjSub, Subgroup.map_sup]
      _ = P ⊔ Work.GW2.conjSub c Kp := by rw [hcP]
      _ ≤ P ⊔ Work.GW2.layerIn h.D.M :=
            sup_le_sup_left hmapKp P
  have hZcard : Nat.card ↥Z = p := by
    rw [hZeq', Work.GW2.conjSub,
      Subgroup.card_map_of_injective (MulAut.conj (c * g)).injective, hPcard]
  refine ⟨hZX, ⟨hZE, ⟨c * g, hZeq'⟩⟩, hZcard, ?_⟩
  exact hZE.trans (Work.CORE4.sup_le_centralizer_P h hPF)

end Work.CORE4
