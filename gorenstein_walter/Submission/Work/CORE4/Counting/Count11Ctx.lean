import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2CountAssembly
import Submission.Work.CORE4.Counting.ElevenGW
import Submission.Work.CORE4.Counting.EConjLayerIn
import Submission.Work.CORE4.Case2CountPieces
import Submission.Work.CORE4.Case2EightAllOfCtx
import Submission.Work.CORE4.Case2KmulS0
import Submission.Work.CORE4.Counting.XsetCount
import Submission.Work.CORE4.Case2EightObjExists
import Submission.Work.CORE4.Case2EightA_le_FsupK0
import Submission.Work.CORE4.Case2EHcard

namespace Work.CORE4.Counting

/-- Counting subgroups of a given order contained in a fixed subgroup `E`: the subgroups of `G`
inside `E` correspond to the subgroups of the group `↥E` (`Y ↦ Y.subgroupOf E`, with inverse
`Z ↦ Z.map E.subtype`). -/
private lemma ncard_subgroups_le_of_le_E {G : Type} [Group G] (E : Subgroup G) (r : ℕ) :
    {Y : Subgroup G | Y ≤ E ∧ Nat.card ↥Y = r}.ncard =
      {Y : Subgroup ↥E | Nat.card ↥Y = r}.ncard := by
  refine Set.ncard_congr (fun Y _ => Y.subgroupOf E) ?_ ?_ ?_
  · intro Y hY
    simp only [Set.mem_setOf_eq] at hY ⊢
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY.1).toEquiv, hY.2]
  · intro Y₁ Y₂ hY₁ hY₂ h
    have h1 : Subgroup.map E.subtype (Y₁.subgroupOf E) =
        Subgroup.map E.subtype (Y₂.subgroupOf E) := by rw [h]
    rwa [Subgroup.map_subgroupOf_eq_of_le hY₁.1, Subgroup.map_subgroupOf_eq_of_le hY₂.1] at h1
  · intro Z hZ
    refine ⟨Subgroup.map E.subtype Z, ⟨Subgroup.map_subtype_le Z, ?_⟩, ?_⟩
    · rw [Subgroup.card_map_of_injective (fun x y h => by simpa using h), hZ]
    · ext x
      constructor
      · intro hx
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hx
        obtain ⟨y, hy, hyx⟩ := hx
        rw [← Subtype.ext hyx]
        exact hy
      · intro hx
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
        exact ⟨x, hx, rfl⟩

/-- **Bender 1981, §4 (11) at the interface of the (12) leaf.**

With `E := layerIn h.D.M` (Bender's `E(M)`), `q := qOf h`, `k` even and `k'` odd the two halves of
`q ∓ 1` with `k = |K| |S₀|`, `p` an odd prime with `P ≤ D.F` of order `p`, and `A` the unique
`(p,p)`-subgroup of `F ⊔ K` containing `P` (so `A = P ⊔ Kp` with `Kp ≤ K₀` of order `p`, available
because `p ∣ |K₀|`), the subgroup `P ⊔ E` contains exactly
`(p₁ − 1) |M : M ⊓ H| + 1` conjugates of `P`, where `p₁ = Case2EightP1 P A` is the number of
`G`-conjugates of `P` inside `A`.

Route (`Work.CORE4.Counting.ElevenGW` is this statement with its pieces supplied; the needed
lemmas are all sorry-free):
* `p ∣ |K₀|` and `K₀ ≤ K` with `K` cyclic give `Kp ≤ K₀` of order `p`
  (`Work.CORE4.CyclicOmegaPrime` + `omegaPrime_le_of_card_dvd`), and `p ∣ k = |K| |S₀|`; `Odd p`
  follows since `|K₀| ∣ |U|` and `U` is odd;
* `P ⊓ Kp = ⊥` and `P`, `Kp` commute (`[F, K] = 1`), so `P ⊔ Kp` is a `(p,p)`-subgroup of `F ⊔ K`
  containing `P`; by the uniqueness conjunct of `Case2EightObj`, `P ⊔ Kp = A` (already proved as
  `Work.CORE4.EightAeqOmega`), whence `{X : X ≤ A ∧ X ~ P} = conjIn P Kp p` (conjugates of `P`
  have order `p`);
* the order-`p` subgroups of `E` are all `E`-conjugate (`Work.CORE4.Counting.EConjLayerIn`);
* `#{Y ≤ E : |Y| = p} = q k'` (`Work.CORE4.L2PrimeCountTransfer` from `I.l2primeCount`);
* `|M : M ⊓ H| = q k'` is the last hypothesis.

Then `ElevenGW` gives exactly the conclusion. -/
theorem Count11Ctx (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) (k k' p : ℕ)
        (P A : Subgroup G),
        Even k → Odd k' →
        ((2 * k = Work.CORE4.qOf h + 1 ∧ 2 * k' = Work.CORE4.qOf h - 1) ∨
          (2 * k = Work.CORE4.qOf h - 1 ∧ 2 * k' = Work.CORE4.qOf h + 1)) →
        k = Nat.card ↥h.D.K * Nat.card ↥B.S0 →
        p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
        Work.GW2.Case2EightObj h.D p P A →
        Odd (Work.CORE4.qOf h) → 7 ≤ Work.CORE4.qOf h → p ∣ Nat.card ↥h.D.K0 →
        (h.D.M ⊓ B.H).relIndex h.D.M = Work.CORE4.qOf h * k' →
        {X : Subgroup G | X ≤ P ⊔ Work.GW2.layerIn h.D.M ∧
            ∃ g : G, X = Work.GW2.conjSub g P}.ncard =
          (Work.GW2.Case2EightP1 P A - 1) * (h.D.M ⊓ B.H).relIndex h.D.M + 1 := by
  intro G _ _ hbc B h k k' p P A hkeven hk'odd hdisj hkK hp hPF hPcard hObj hqodd hq7 hpK0 hrel
  -- §4 (9): `E(M) ≃* L₂(q)` with `q = nineP h ^ nineK h = qOf h`
  haveI : Fact (Work.CORE4.nineP h).Prime := ⟨Work.CORE4.nineP_prime h⟩
  obtain ⟨φ⟩ := Work.CORE4.nineP_iso (B := B) h
  have hdisj' : (2 * k = Work.CORE4.nineP h ^ Work.CORE4.nineK h + 1 ∧
        2 * k' = Work.CORE4.nineP h ^ Work.CORE4.nineK h - 1) ∨
      (2 * k = Work.CORE4.nineP h ^ Work.CORE4.nineK h - 1 ∧
        2 * k' = Work.CORE4.nineP h ^ Work.CORE4.nineK h + 1) := by
    simpa only [Work.CORE4.qOf] using hdisj
  have h5 : 5 ≤ Work.CORE4.nineP h ^ Work.CORE4.nineK h := by
    have h7' : 7 ≤ Work.CORE4.nineP h ^ Work.CORE4.nineK h := by
      simpa only [Work.CORE4.qOf] using hq7
    omega
  -- `p ∣ |F|`, and the `p`-torsion `Kp` of the cyclic `K` lies in `K₀ ≤ K ≤ E(M)`
  have hpF : p ∣ Nat.card ↥h.D.F := by
    rw [← hPcard]
    exact Subgroup.card_dvd_of_le hPF
  have hK0_le_K : h.D.K0 ≤ h.D.K := show h.D.K0 ≤ h.D.K from inf_le_right
  have hpK : p ∣ Nat.card ↥h.D.K := hpK0.trans (Subgroup.card_dvd_of_le hK0_le_K)
  obtain ⟨Kp, hKp_le_K, hKp_card, hKp_omega⟩ :=
    Work.CORE4.CyclicOmegaPrime h.D.K p h.pre.K_cyclic hp hpK
  have hKp_le_K0 : Kp ≤ h.D.K0 :=
    Work.CORE4.omegaPrime_le_of_card_dvd (K := h.D.K) (K0 := h.D.K0) (Kp := Kp) hp
      hK0_le_K hpK0 hKp_card hKp_omega
  have hKp_le_E : Kp ≤ Work.GW2.layerIn h.D.M :=
    (hKp_le_K0.trans hK0_le_K).trans (Work.CORE4.K_le_layerIn B h)
  -- `p` is odd: `p ∣ |K₀| ∣ |U|` and `U` has odd order
  have hoddp : Odd p :=
    Odd.of_dvd_nat B.U_odd (hpK0.trans (Subgroup.card_dvd_of_le
      (hK0_le_K.trans (Work.GW2.Case2Data.K_le_U B h.D))))
  -- `p ∣ k = |K| |S₀|`
  have hpdivk : p ∣ k := by
    rw [hkK]
    exact dvd_mul_of_dvd_left (hpK0.trans (Subgroup.card_dvd_of_le hK0_le_K)) _
  -- the `p`-torsion of the cyclic `F` is `P`
  obtain ⟨Fp, hFp_le, hFp_card, hFp_omega⟩ :=
    Work.CORE4.CyclicOmegaPrime h.D.F p h.F_cyclic hp hpF
  have hP_le_Fp : P ≤ Fp := fun x hx =>
    (hFp_omega x (hPF hx)).mp (Work.CORE4.pow_eq_one_of_card_eq hPcard hx)
  have hPFp : P = Fp :=
    Subgroup.eq_of_le_of_card_ge hP_le_Fp (by rw [hFp_card, hPcard])
  have hP_omega : ∀ x ∈ h.D.F, x ^ p = 1 ↔ x ∈ P := by
    intro x hx
    rw [hPFp]
    exact hFp_omega x hx
  -- §4 (8): `A` is the unique `(p,p)`-subgroup of `F ⊔ K` containing `P`, hence `A = P ⊔ Kp`
  obtain ⟨-, hPK_le, hPK_card, hPK_exp, -⟩ :=
    Work.CORE4.Case2EightPpSupUnique h.D.F h.D.K P Kp p
      (Work.CORE4.F_inf_K_eq_bot_c4 B h.D)
      (Work.CORE4.F_le_normalizer_K_c4 I B h.D)
      (Work.CORE4.F_commute_K_c4 I B h.D h.pre)
      hPF hKp_le_K hP_omega hKp_omega hPcard hKp_card
  have hAeq : A = P ⊔ Kp :=
    (hObj.2.2.2.2.2.2.2 (P ⊔ Kp) hPK_le hPK_card hPK_exp).symm
  -- the fibre over `Kp` contains exactly `p₁ = Case2EightP1 P A` conjugates of `P`
  have hbase : (conjIn P Kp p).ncard = Work.GW2.Case2EightP1 P A := by
    have hset : conjIn P Kp p =
        {X : Subgroup G | X ≤ P ⊔ Kp ∧ ∃ g : G, X = Work.GW2.conjSub g P} := by
      ext X
      exact ⟨fun hx => ⟨hx.2.1, hx.2.2⟩,
        fun hx => ⟨(by obtain ⟨g, rfl⟩ := hx.2; exact (conjSub_card g P).trans hPcard),
          hx.1, hx.2⟩⟩
    have hP1 : Work.GW2.Case2EightP1 P A =
        {X : Subgroup G | X ≤ A ∧ ∃ g : G, X = Work.GW2.conjSub g P}.ncard := rfl
    rw [hset, hP1, hAeq]
  -- transitivity of `E(M)` on its order-`p` subgroups (Bender: `E` has cyclic `S_p`-subgroups)
  have hconj : ∀ Y : Subgroup G, Y ≤ Work.GW2.layerIn h.D.M → Nat.card ↥Y = p →
      ∃ e ∈ Work.GW2.layerIn h.D.M, Y = Work.GW2.conjSub e Kp := by
    intro Y hYE hYcard
    exact EConjLayerIn I G B h (Work.CORE4.nineP h) (Work.CORE4.nineK h) k k'
      ⟨Work.CORE4.nineP_prime h⟩ φ p (Work.CORE4.nineP_odd h) h5 hkeven hk'odd hdisj' hp hoddp
      hpdivk Kp Y hKp_le_E hYE hKp_card hYcard
  -- §4 (11), first half: `E(M)` has `q k'` subgroups of order `p`
  have hpne2 : p ≠ 2 := by
    intro h2
    rw [h2] at hoddp
    obtain ⟨m, hm⟩ := hoddp
    omega
  have hcountE : {Y : Subgroup ↥(Work.GW2.layerIn h.D.M) | Nat.card Y = p}.ncard =
      Work.CORE4.qOf h * k' :=
    L2PrimeCountTransfer I G B h (Work.CORE4.nineP h) (Work.CORE4.nineK h)
      ⟨Work.CORE4.nineP_prime h⟩ φ (Work.CORE4.qOf h) k k' p (Work.CORE4.nineP_odd h) h5 rfl
      hkeven hk'odd hdisj hp hpne2 hpdivk
  have hcount : {Y : Subgroup G | Y ≤ Work.GW2.layerIn h.D.M ∧ Nat.card ↥Y = p}.ncard =
      (h.D.M ⊓ B.H).relIndex h.D.M := by
    rw [ncard_subgroups_le_of_le_E (Work.GW2.layerIn h.D.M) p, hcountE]
    exact hrel.symm
  -- Bender §4 (11)
  have h11 := ElevenGW I G hbc B h p (Work.GW2.Case2EightP1 P A)
    ((h.D.M ⊓ B.H).relIndex h.D.M) P Kp hp hPF hPcard hKp_le_K0 hKp_card hconj hbase hcount
  -- every conjugate of `P` has order `p`, so the order condition is automatic
  have hset2 : {X : Subgroup G | X ≤ P ⊔ Work.GW2.layerIn h.D.M ∧
        ∃ g : G, X = Work.GW2.conjSub g P} =
      {X : Subgroup G | Nat.card ↥X = p ∧ X ≤ P ⊔ Work.GW2.layerIn h.D.M ∧
        ∃ g : G, X = Work.GW2.conjSub g P} := by
    ext X
    exact ⟨fun hx => ⟨(by obtain ⟨g, rfl⟩ := hx.2; exact (conjSub_card g P).trans hPcard),
        hx.1, hx.2⟩,
      fun hx => ⟨hx.2.1, hx.2.2⟩⟩
  rw [hset2]
  exact h11

end Work.CORE4.Counting
