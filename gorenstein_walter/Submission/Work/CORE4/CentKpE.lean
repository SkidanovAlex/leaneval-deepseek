import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2KmulS0
import Submission.Work.CORE4.Case2EHcard
import Submission.Work.CORE4.S0CentK
import Submission.Work.CORE4.Counting.EConjLayerIn
import Submission.Work.CORE4.KmulS0Tied
import Submission.Work.CORE4.Counting.CardCentralizerMap
import Submission.Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot

namespace Work.CORE4

open scoped MatrixGroups

open Subgroup

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-! ## Elementary helpers -/

/-- Arithmetic: if `2 d` and `2 c` are each one of `q ± 1` and `d ∣ c` with `d > 1`, then
`d = c` (the two halves of `q ± 1` are coprime). -/
theorem CentKpE_two_mul_eq {q d c : ℕ} (hd : 2 * d = q + 1 ∨ 2 * d = q - 1)
    (hc : 2 * c = q + 1 ∨ 2 * c = q - 1) (hdvd : d ∣ c) (h1 : 1 < d) : d = c := by
  rcases hd with hd | hd <;> rcases hc with hc | hc
  · omega
  · exfalso
    have hdc : d = c + 1 := by omega
    have hsub : d - c = 1 := by omega
    have h := Nat.dvd_sub (dvd_refl d) hdvd
    rw [hsub] at h
    have := Nat.dvd_one.mp h
    omega
  · exfalso
    have hcd : c = d + 1 := by omega
    have hsub : c - d = 1 := by omega
    have h := Nat.dvd_sub hdvd (dvd_refl d)
    rw [hsub] at h
    have := Nat.dvd_one.mp h
    omega
  · omega

/-- A cyclic subgroup centralizes any subgroup it contains. -/
theorem CentKpE_le_centralizer_of_isCyclic {G : Type*} [Group G] {K Kp : Subgroup G}
    (h : IsCyclic ↥K) (hKp : Kp ≤ K) : K ≤ Subgroup.centralizer (Kp : Set G) := by
  haveI : IsCyclic ↥K := h
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥K)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hKp hy⟩)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
  have key : (⟨y, hKp hy⟩ : ↥K) * ⟨x, hx⟩ = ⟨x, hx⟩ * ⟨y, hKp hy⟩ := by
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  exact congrArg Subtype.val key

/-! ## The main theorem -/

/-- **Bender 1981, §4, p. 227: `C_E(Kp) = K · S₀`**, where `E := layerIn h.D.M`, `Kp ≤ K₀ = F(U) ⊓ K` is the order-`p` subgroup of the cyclic odd `K` (`p` an odd prime).

Route.  `E ≅ PSL(2, pF^kF)` by §4 (9) (`Case2Ctx.nine`), and `Kp` has prime order `p ∤ q`
(`p ∣ |K| ∣ k` and `2k = q ± 1`), so `I.toolkit.l2torusNorm` (transported along the
isomorphism, as in `Work.CORE4.Counting.EConjLayerIn`) gives `C_E(Kp)` cyclic with
`2 |C_E(Kp)| = q + 1` or `q − 1`, i.e. `|C_E(Kp)| ∈ {k, k'}`.

Now `K ≤ C_E(Kp)` trivially (K is cyclic of odd order and `Ω₁(K) = Kp` via `|Kp| = p`), and
`|K| ∣ k = |K| · |S₀|` with `|K| > 1` and `gcd(k, k') = 1`, so `|C_E(Kp)| = k`.  Also
`S₀ ≤ C_E(Kp)`: this is `⁅K, S₀⁆ = ⊥` (`Work.CORE4.S0CentK`).  Hence `K ⊔ S₀ ≤ C_E(Kp)` with
`|K ⊔ S₀| = |K| · |S₀| = k` (`K ⊓ S₀ = 1`: `K` is odd, `S₀` is a 2-group), and comparing orders
gives `C_E(Kp) = K ⊔ S₀`.

Consequently, with `A = P ⊔ Kp` the `(p,p)`-subgroup of `F ⊔ K` (`P ≤ F` of order `p`,
`P ≤ C_G(E)` since `F ≤ C_G(E)`):
`C_{P⊔E}(A) = P ⊔ C_E(Kp) = P ⊔ K ⊔ S₀` of order `p k`. -/
theorem CentKpE (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) (p : ℕ) (Kp : Subgroup G),
        p.Prime → Kp ≤ Work.GW2.Case2Data.K0 h.D → Nat.card ↥Kp = p →
        Subgroup.centralizer (Kp : Set G) ⊓ Work.GW2.layerIn h.D.M = h.D.K ⊔ B.S0 := by
  intro G _ _ hbc B h p Kp hpp hKpK0 hKpcard
  obtain ⟨pF, kF, hpF, hpFodd, h7, ⟨φ⟩, hSE⟩ := h.nine
  haveI := hpF
  have h5 : 5 ≤ pF ^ kF := by omega
  -- ## (0) `Kp ≤ K`
  have hKpK : Kp ≤ h.D.K := by
    refine le_trans hKpK0 ?_
    exact inf_le_right
  -- ## (1) `K ≤ E = E(M)`, `p ∣ |K|`, `p` odd, `p ≠ 2`
  have hKE : h.D.K ≤ Work.GW2.layerIn h.D.M := K_le_layerIn B h
  have hKpE : Kp ≤ Work.GW2.layerIn h.D.M := le_trans hKpK hKE
  have hpK : p ∣ Nat.card ↥h.D.K := hKpcard ▸ Subgroup.card_dvd_of_le hKpK
  have hpU : Nat.card ↥h.D.K ∣ Nat.card ↥B.U :=
    Subgroup.card_dvd_of_le (Work.GW2.Case2Data.K_le_U B h.D)
  have hpodd : Odd p := Odd.of_dvd_nat B.U_odd (hpK.trans hpU)
  have hp2 : p ≠ 2 := by
    intro h2
    rw [h2] at hpodd
    exact absurd hpodd (by decide)
  -- ## (2) the identity `2 |K| |S₀| = pF ^ kF ± 1`
  have hKmul : (2 * (Nat.card ↥h.D.K * Nat.card ↥B.S0) = pF ^ kF + 1) ∨
      (2 * (Nat.card ↥h.D.K * Nat.card ↥B.S0) = pF ^ kF - 1) :=
    Work.CORE4.KmulS0Tied I hbc h hpF hpFodd h7 φ
  -- ## (3) `p ≠ pF`
  have hpF_ne_p : p ≠ pF := by
    intro hpeq
    have hkF1 : 1 ≤ kF := by
      by_contra hlt
      rw [Nat.not_le] at hlt
      rw [Nat.lt_one_iff.mp hlt, pow_zero] at h7
      omega
    have hd1 : pF ∣ pF ^ kF := ⟨pF ^ (kF - 1), by rw [← pow_succ', Nat.sub_add_cancel hkF1]⟩
    have hdvd : pF ∣ Nat.card ↥h.D.K * Nat.card ↥B.S0 := hpeq ▸ dvd_mul_of_dvd_left hpK _
    have h1 : pF ∣ 2 * (Nat.card ↥h.D.K * Nat.card ↥B.S0) := dvd_mul_of_dvd_right hdvd 2
    have hge : 1 ≤ pF ^ kF := by omega
    rcases hKmul with hk | hk
    · have h2 : pF ∣ 1 := by
        have hsub : pF ^ kF + 1 - pF ^ kF = 1 := by omega
        have h := Nat.dvd_sub (hk ▸ h1 : pF ∣ pF ^ kF + 1) hd1
        rwa [hsub] at h
      have : pF = 1 := Nat.dvd_one.mp h2
      have := hpF.out.two_le
      omega
    · have h2 : pF ∣ 1 := by
        have h1' : pF ∣ pF ^ kF - 1 := hk ▸ h1
        have hsub : pF ^ kF - (pF ^ kF - 1) = 1 := by omega
        have h := Nat.dvd_sub hd1 h1'
        rwa [hsub] at h
      have : pF = 1 := Nat.dvd_one.mp h2
      have := hpF.out.two_le
      omega
  -- ## (4) `K ⊔ S₀ ≤ C_G(Kp) ⊓ E`
  have hKcent : h.D.K ≤ Subgroup.centralizer (Kp : Set G) :=
    CentKpE_le_centralizer_of_isCyclic (Work.GW2.Case2Pre.K_cyclic B h.D h.pre) hKpK
  have hS0centK : h.D.K ≤ Subgroup.centralizer (B.S0 : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (S0CentK I G hbc B h)
  have hS0cent : B.S0 ≤ Subgroup.centralizer (Kp : Set G) := by
    have h2 : B.S0 ≤ Subgroup.centralizer ((h.D.K : Subgroup G) : Set G) :=
      Subgroup.le_centralizer_iff.mp hS0centK
    refine le_trans h2 (Subgroup.centralizer_le ?_)
    intro y hy
    exact hKpK hy
  have hle : h.D.K ⊔ B.S0 ≤
      Subgroup.centralizer (Kp : Set G) ⊓ Work.GW2.layerIn h.D.M :=
    sup_le (le_inf hKcent hKE) (le_inf hS0cent (le_trans B.S0_le hSE))
  -- ## (5) `|K ⊔ S₀| = |K| |S₀|`
  have hcardSup : Nat.card ↥(h.D.K ⊔ B.S0) = Nat.card ↥h.D.K * Nat.card ↥B.S0 := by
    refine Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot ?_ ?_
    · rw [Subgroup.le_normalizer_iff]
      intro s hs y hy
      have h2 : B.S0 ≤ Subgroup.centralizer ((h.D.K : Subgroup G) : Set G) :=
        Subgroup.le_centralizer_iff.mp hS0centK
      have hcomm : y * s = s * y := Subgroup.mem_centralizer_iff.mp (h2 hs) y hy
      have hsy : s * y * s⁻¹ = y := by rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [hsy]
      exact hy
    · rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      obtain ⟨hxK, hxS0⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_bot.mp ?_
      rw [← B.U_inf_S]
      exact Subgroup.mem_inf.mpr ⟨h.D.K_le_U B hxK, B.S0_le hxS0⟩
  -- ## (6) the image `Y` of `Kp` in `PSL(2, pF^kF)` and `l2torusNorm`
  have hcardKpE : Nat.card ↥(Kp.subgroupOf (Work.GW2.layerIn h.D.M)) = p := by
    rw [← Subgroup.card_map_of_injective (K := Kp.subgroupOf (Work.GW2.layerIn h.D.M))
        (f := (Work.GW2.layerIn h.D.M).subtype) (Subgroup.subtype_injective _),
      Subgroup.map_subgroupOf_eq_of_le hKpE, hKpcard]
  set Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)) :=
    (Kp.subgroupOf (Work.GW2.layerIn h.D.M)).map φ.toMonoidHom with hY
  have hYcard : Nat.card ↥Y = p := by
    rw [hY, Subgroup.card_map_of_injective φ.injective, hcardKpE]
  obtain ⟨_hCcyc, hChalf, _hCnorm⟩ :=
    I.l2torusNorm pF kF hpFodd h5 p hpp hp2 hpF_ne_p Y hYcard
  -- ## (7) transport the centralizer cardinality
  have htransport :
      Nat.card ↥(Subgroup.centralizer (Kp : Set G) ⊓ Work.GW2.layerIn h.D.M) =
        Nat.card ↥(Subgroup.centralizer
          (Y : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))) := by
    have hstep1 : (Subgroup.centralizer (Kp : Set G) ⊓
          Work.GW2.layerIn h.D.M).subgroupOf (Work.GW2.layerIn h.D.M) =
        Subgroup.centralizer
          ((Kp.subgroupOf (Work.GW2.layerIn h.D.M)) : Set ↥(Work.GW2.layerIn h.D.M)) := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyG : (y : G) ∈ Kp :=
          Subgroup.mem_subgroupOf.mp (show y ∈ (Kp.subgroupOf (Work.GW2.layerIn h.D.M) :
            Subgroup ↥(Work.GW2.layerIn h.D.M)) from hy)
        have hx1 := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1
        have hmem := Subgroup.mem_centralizer_iff.mp hx1 (y : G) hyG
        apply Subtype.ext
        exact hmem
      · intro hx
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        refine ⟨?_, x.2⟩
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyK : (⟨y, hKpE hy⟩ : ↥(Work.GW2.layerIn h.D.M)) ∈
            (Kp.subgroupOf (Work.GW2.layerIn h.D.M) : Subgroup ↥(Work.GW2.layerIn h.D.M)) :=
          Subgroup.mem_subgroupOf.mpr (show y ∈ Kp from hy)
        exact congrArg Subtype.val
          (Subgroup.mem_centralizer_iff.mp hx
            (⟨y, hKpE hy⟩ : ↥(Work.GW2.layerIn h.D.M)) hyK)
    calc Nat.card ↥(Subgroup.centralizer (Kp : Set G) ⊓ Work.GW2.layerIn h.D.M)
        = Nat.card ↥((Subgroup.centralizer (Kp : Set G) ⊓
            Work.GW2.layerIn h.D.M).subgroupOf (Work.GW2.layerIn h.D.M)) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
            Subgroup.centralizer (Kp : Set G) ⊓ Work.GW2.layerIn h.D.M ≤
              Work.GW2.layerIn h.D.M)).toEquiv).symm
      _ = Nat.card ↥(Subgroup.centralizer
            ((Kp.subgroupOf (Work.GW2.layerIn h.D.M)) : Set ↥(Work.GW2.layerIn h.D.M))) := by
          rw [hstep1]
      _ = Nat.card ↥(Subgroup.centralizer
            (Y : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))) := by
          rw [hY]
          exact (Work.CORE4.Counting.CardCentralizerMap φ (Kp.subgroupOf (Work.GW2.layerIn h.D.M))).symm
  -- ## (8) the card of `C_G(Kp) ⊓ E` equals `|K| |S₀|`
  have hC2 : 2 * Nat.card ↥(Subgroup.centralizer (Kp : Set G) ⊓ Work.GW2.layerIn h.D.M) =
        pF ^ kF + 1 ∨
      2 * Nat.card ↥(Subgroup.centralizer (Kp : Set G) ⊓ Work.GW2.layerIn h.D.M) =
        pF ^ kF - 1 := by
    rw [htransport]
    exact hChalf
  have hdvd : Nat.card ↥h.D.K * Nat.card ↥B.S0 ∣
      Nat.card ↥(Subgroup.centralizer (Kp : Set G) ⊓ Work.GW2.layerIn h.D.M) := by
    rw [← hcardSup]
    exact Subgroup.card_dvd_of_le hle
  have h1d : 1 < Nat.card ↥h.D.K * Nat.card ↥B.S0 := by
    have hp2le : 2 ≤ p := hpp.two_le
    have hpKle : p ≤ Nat.card ↥h.D.K := Nat.le_of_dvd Nat.card_pos hpK
    have hS0pos : 1 ≤ Nat.card ↥B.S0 := Nat.card_pos
    calc (1 : ℕ) < 2 * 1 := by norm_num
      _ ≤ Nat.card ↥h.D.K * Nat.card ↥B.S0 := Nat.mul_le_mul (le_trans hp2le hpKle) hS0pos
  have hdeq : Nat.card ↥h.D.K * Nat.card ↥B.S0 =
      Nat.card ↥(Subgroup.centralizer (Kp : Set G) ⊓ Work.GW2.layerIn h.D.M) :=
    CentKpE_two_mul_eq hKmul hC2 hdvd h1d
  -- ## (9) conclude
  have hcardfinal : Nat.card ↥(Subgroup.centralizer (Kp : Set G) ⊓ Work.GW2.layerIn h.D.M) =
      Nat.card ↥(h.D.K ⊔ B.S0) := by
    rw [hcardSup]
    exact hdeq.symm
  exact (Subgroup.eq_of_le_of_card_ge hle hcardfinal.le).symm

end Work.CORE4
