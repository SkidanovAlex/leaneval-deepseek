import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.piCore_isPiNat
import Submission.Work.Fitting.piCore_quotient_eq_bot
import Submission.Work.Fitting.isPSolvable_quotient
import Submission.Work.Fitting.isPSolvable_subgroup
import Submission.Work.Fitting.fitting_eq_iSup_pCore
import Submission.Work.Fitting.pCore_le_fitting
import Submission.Work.Fitting.pCoreSeries_one
import Submission.Work.Fitting.pCoreSeries_two
import Submission.Work.Fitting.pCoreSeries_mono
import Submission.Work.Fitting.pCore_le_pPrimePCore
import Submission.Work.Fitting.isMinimalNormal_isPGroup_or_pPrime
import Submission.Work.Fitting.isMinimalNormal_isPGroup_commutative
import Submission.Work.Fitting.fitting_eq_pCore_of_pPrimeCore_eq_bot
import Submission.Work.Fitting.exists_isMinimalNormal_le
import Submission.Work.Fitting.isNilpotent_of_commutator_le_center
import Submission.Work.Fitting.pPrimeCore_eq_top_of_not_prime
import Submission.Work.Fitting.mem_sectionCentralizer_iff_commutator
import Submission.Work.HallHigman.piCore_isPiNat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `C_G(O_{p',p}(G)/O_{p'}(G)) ≤ O_{p',p}(G)`

For a finite `p`-solvable group `G` the centralizer of the section `O_{p',p}(G)/O_{p'}(G)`
is contained in `O_{p',p}(G)`.

The proof reduces to the quotient `X = G/O_{p'}(G)`, where `O_{p'}(X) = 1`; the statement
becomes `C_X(O_p(X)) ≤ O_p(X)`, which is proved by strong induction on `|X|`.
-/

noncomputable section

set_option linter.style.haveILetI false

open Classical

namespace Work.Fitting

/-- The `π`-core of a trivial group is trivial. -/
private theorem piCore_eq_bot_of_subsingleton {π : ℕ → Prop} (Y : Type*) [Group Y]
    [Subsingleton Y] : piCore π Y = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [piCore]
  refine sSup_le ?_
  intro N _
  refine le_bot_iff.mpr ?_
  rw [Subgroup.eq_bot_iff_forall]
  intro y _
  exact Subsingleton.elim y 1

/-- If `O_p(G) = O_{p'}(G) = 1` and `G` is `p`-solvable, then `G` is trivial: the upper
`p`-series of `G` is constant, since each step only involves `O_p` and `O_{p'}` of `G`
itself. -/
private theorem subsingleton_of_core_eq_bot (p : ℕ) (G : Type*) [Group G] [Finite G]
    (hps : IsPSolvable p G) (h1 : pCore p G = ⊥) (h2 : pPrimeCore p G = ⊥) :
    Subsingleton G := by
  have hconst : ∀ k, pCoreSeries p G k = ⊥ := by
    intro k
    induction k with
    | zero => exact pCoreSeries_zero p G
    | succ k ih =>
      haveI : Finite (G ⧸ pCoreSeries p G k) :=
        Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
      have hinj : Function.Injective (QuotientGroup.mk' (pCoreSeries p G k)) := by
        rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
        exact ih
      rw [pCoreSeries_succ,
        piCore_comap_of_bijective (π := fun q => if Even k then q ≠ p else q = p)
          (f := QuotientGroup.mk' (pCoreSeries p G k)) hinj (QuotientGroup.mk'_surjective _)]
      by_cases hk : Even k
      · have hπ : (fun q : ℕ => if Even k then q ≠ p else q = p) = fun q => q ≠ p := by
          funext q; simp [hk]
        rw [hπ]; exact h2
      · have hπ : (fun q : ℕ => if Even k then q ≠ p else q = p) = fun q => q = p := by
          funext q; simp [hk]
        rw [hπ]; exact h1
  obtain ⟨n, hn⟩ := hps.out
  have hbot : (⊥ : Subgroup G) = ⊤ := by rw [← hconst n, hn]
  refine ⟨fun x y => ?_⟩
  have hx : x = 1 := Subgroup.mem_bot.mp (by rw [hbot]; exact Subgroup.mem_top x)
  have hy : y = 1 := Subgroup.mem_bot.mp (by rw [hbot]; exact Subgroup.mem_top y)
  rw [hx, hy]

/-- `O_{p',p}(G) = G` as soon as `O_{p'}(G) = G`. -/
private theorem pPrimePCore_eq_top_of_pPrimeCore_eq_top (p : ℕ) (G : Type*) [Group G]
    (h : pPrimeCore p G = ⊤) : pPrimePCore p G = ⊤ := by
  haveI : Subsingleton (G ⧸ pPrimeCore p G) := QuotientGroup.subsingleton_iff.mpr h
  rw [pPrimePCore, piCore_eq_bot_of_subsingleton, MonoidHom.comap_bot, QuotientGroup.ker_mk',
    h]

/-- **Key step.**  If `X` is a finite `p`-solvable group with `O_{p'}(X) = 1` then
`C_X(O_p(X)) ≤ O_p(X)`.  Proved by strong induction on `|X|`. -/
private theorem centralizer_pCore_le_aux (p : ℕ) (hp : p.Prime) (n : ℕ) :
    ∀ (X : Type*) [Group X] [Finite X], Nat.card X ≤ n → IsPSolvable p X →
      pPrimeCore p X = ⊥ →
      Subgroup.centralizer ((pCore p X : Subgroup X) : Set X) ≤ pCore p X := by
  induction n with
  | zero =>
    intro X _ _ hcard _ _
    have hpos : 0 < Nat.card X := Nat.card_pos
    omega
  | succ n ih =>
    intro X _ _ hcard hps hcore
    haveI := hps
    by_cases hsmall : Nat.card X ≤ n
    · exact ih X hsmall hps hcore
    · have hbig : n < Nat.card X := not_le.mp hsmall
      have hXcard : Nat.card X = n + 1 := le_antisymm hcard (Nat.succ_le_of_lt hbig)
      let P : Subgroup X := pCore p X
      let C : Subgroup X := Subgroup.centralizer ((P : Subgroup X) : Set X)
      have hPnorm : P.Normal := inferInstance
      have hCnorm : C.Normal := Subgroup.normal_centralizer (H := P)
      change C ≤ P
      by_cases hCP : C ≤ P
      · exact hCP
      · by_cases hPbot : P = ⊥
        · -- `O_p(X) = 1` and `O_{p'}(X) = 1` force `X` to be trivial
          have hsub : Subsingleton X := subsingleton_of_core_eq_bot p X hps hPbot hcore
          intro x _
          rw [hPbot]
          exact Subgroup.mem_bot.mpr (Subsingleton.elim x 1)
        · -- main case: `O_p(X) ≠ 1`
          exfalso
          let Z : Subgroup X := C ⊓ P
          have hZnorm : Z.Normal := inferInstance
          have hZleP : Z ≤ P := inf_le_right
          have hZleC : Z ≤ C := inf_le_left
          let q : X →* X ⧸ Z := QuotientGroup.mk' Z
          have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective Z
          have hkerq : q.ker = Z := QuotientGroup.ker_mk' Z
          haveI : Finite (X ⧸ Z) := Finite.of_surjective _ hqsurj
          haveI : IsPSolvable p (X ⧸ Z) := isPSolvable_quotient p X Z
          -- `[Z, N] = 1` for every `N ≤ C`
          have hZcent : ∀ {N : Subgroup X}, N ≤ C → ⁅Z, N⁆ = ⊥ := by
            intro N hN
            rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
            intro z hz
            rw [Subgroup.mem_centralizer_iff]
            intro x hx
            exact (Subgroup.mem_centralizer_iff.mp (hN hx) z (hZleP hz)).symm
          have hCbne : C.map q ≠ ⊥ := by
            intro h
            apply hCP
            have h' : C ≤ q.ker := (Subgroup.map_eq_bot_iff C).mp h
            rw [hkerq] at h'
            exact h'.trans inf_le_right
          have hCbnorm : (C.map q).Normal := Subgroup.Normal.map hCnorm q hqsurj
          obtain ⟨Nb, hNbmin, hNb_le⟩ := exists_isMinimalNormal_le (X ⧸ Z) hCbnorm hCbne
          have hNbnorm : Nb.Normal := hNbmin.1
          have hNbne : Nb ≠ ⊥ := hNbmin.2.1
          let N : Subgroup X := Nb.comap q
          have hNnorm : N.Normal := Subgroup.normal_comap q
          have hN_le_C : N ≤ C := by
            intro x hx
            have hx' : q x ∈ C.map q := hNb_le hx
            have hx'' : x ∈ Subgroup.comap q (Subgroup.map q C) := hx'
            rw [Subgroup.comap_map_eq, hkerq, sup_eq_left.mpr hZleC] at hx''
            exact hx''
          have hN_map : N.map q = Nb := Subgroup.map_comap_eq_self_of_surjective hqsurj Nb
          have hZ_le_N : Z ≤ N := by
            intro z hz
            rw [Subgroup.mem_comap]
            have hz' : q z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
            rw [hz']
            exact Nb.one_mem
          have hcardN : Nat.card ↥N = Nat.card ↥Z * Nat.card ↥Nb := by
            have h := card_comap_eq_card_ker_mul q hqsurj Nb
            rwa [hkerq] at h
          have hN_ne_Z : N ≠ Z := by
            intro h
            apply hNbne
            rw [← hN_map, h]
            rw [Subgroup.map_eq_bot_iff]
            intro z hz
            rw [hkerq]
            exact hz
          by_cases hNX : N = ⊤
          · -- Case `N = X`: then `X ≤ C_X(P)`, `Z = P`, and `X ⧸ Z` is simple
            have hCtop : C = ⊤ := le_antisymm le_top (by rw [← hNX]; exact hN_le_C)
            have hZP : Z = P := by
              show C ⊓ P = P
              rw [hCtop, top_inf_eq]
            have hNb_top : Nb = ⊤ := by
              rw [← hN_map, hNX]
              exact Subgroup.map_top_of_surjective q hqsurj
            have hsimple : ∀ M : Subgroup (X ⧸ Z), M.Normal → M ≠ ⊥ → M = ⊤ := by
              intro M hMn hMne
              have h := hNbmin.2.2 M hMn (by rw [hNb_top]; exact le_top) hMne
              rwa [hNb_top] at h
            have hmin_top : IsMinimalNormal (⊤ : Subgroup (X ⧸ Z)) :=
              ⟨inferInstance, fun h => hNbne (hNb_top.trans h),
                fun M hMn _ hMne => hsimple M hMn hMne⟩
            have hPpi : IsPiNat (fun r => r = p) (Nat.card ↥P) :=
              (isPiNat_prime_iff_isPGroup hp P).mpr (isPGroup_pCore hp)
            rcases isMinimalNormal_isPGroup_or_pPrime p (X ⧸ Z) hmin_top with hpg | hpp
            · -- `X ⧸ Z` is a `p`-group, so `X` is a `p`-group and `X = P = Z`
              rw [Subgroup.card_top] at hpg
              have hXpi : IsPiNat (fun r => r = p) (Nat.card ↥(⊤ : Subgroup X)) := by
                rw [Subgroup.card_top, Subgroup.card_eq_card_quotient_mul_card_subgroup Z]
                exact IsPiNat.mul hpg (by rw [hZP]; exact hPpi)
              have hXleP : (⊤ : Subgroup X) ≤ Z := by
                rw [hZP]
                exact le_piCore Subgroup.normal_top hXpi
              haveI : Subsingleton (X ⧸ Z) :=
                QuotientGroup.subsingleton_iff.mpr (le_antisymm hXleP le_top).symm
              exact hNbne (le_bot_iff.mp fun x _ =>
                Subgroup.mem_bot.mpr (Subsingleton.elim x 1))
            · -- `X ⧸ Z` is a `p'`-group: Schur–Zassenhaus
              rw [Subgroup.card_top] at hpp
              obtain ⟨k, hk⟩ := (isPiNat_prime_iff hp).mp hPpi
              have hquot : Nat.card (X ⧸ P) = Nat.card (X ⧸ Z) := by rw [hZP]
              have hcop : Nat.Coprime (Nat.card ↥P) P.index := by
                rw [hk, Subgroup.index_eq_card, hquot]
                refine Nat.Coprime.pow_left _ ?_
                rw [Nat.Prime.coprime_iff_not_dvd hp]
                intro hdvd
                exact hpp p hp hdvd rfl
              obtain ⟨H, hHc⟩ := Subgroup.exists_right_complement'_of_coprime (N := P) hcop
              -- `P` is central in `X`, hence `H` is normal
              have hcent_top : (⊤ : Subgroup X) ≤ Subgroup.centralizer ((P : Subgroup X) : Set X) := by
                rw [← hCtop]
              have hcc : ∀ y ∈ P, ∀ z : X, y * z = z * y := fun y hy z =>
                Subgroup.mem_centralizer_iff.mp (hcent_top (Subgroup.mem_top z)) y hy
              have hHnorm : H.Normal := by
                refine Subgroup.Normal.mk ?_
                intro h hh x
                obtain ⟨y, hyP, h1, h1H, rfl⟩ := (Subgroup.mem_sup_of_normal_left).mp (by
                  rw [hHc.sup_eq_top]; exact Subgroup.mem_top x)
                rw [mul_inv_rev]
                have h2 : y * (h1 * h * h1⁻¹) = (h1 * h * h1⁻¹) * y := hcc y hyP _
                have heq : y * h1 * h * (h1⁻¹ * y⁻¹) = h1 * h * h1⁻¹ := by
                  calc y * h1 * h * (h1⁻¹ * y⁻¹)
                      = y * (h1 * h * h1⁻¹) * y⁻¹ := by group
                    _ = (h1 * h * h1⁻¹) * y * y⁻¹ := by rw [h2]
                    _ = h1 * h * h1⁻¹ := by group
                rw [heq]
                exact H.mul_mem (H.mul_mem h1H hh) (H.inv_mem h1H)
              have hHne : H ≠ ⊥ := by
                intro hbot
                have hcard : Nat.card ↥P * Nat.card ↥H = Nat.card X := hHc.card_mul_card
                rw [hbot, Subgroup.card_bot, mul_one] at hcard
                have hPtop : P = ⊤ := Subgroup.eq_of_le_of_card_ge le_top
                  (by rw [Subgroup.card_top]; exact le_of_eq hcard.symm)
                have htop : (⊤ : Subgroup X) = Z := by rw [hZP, hPtop]
                haveI : Subsingleton (X ⧸ Z) := QuotientGroup.subsingleton_iff.mpr htop.symm
                exact hNbne (le_bot_iff.mp fun x _ =>
                  Subgroup.mem_bot.mpr (Subsingleton.elim x 1))
              have hHpi : IsPiNat (fun r => r ≠ p) (Nat.card ↥H) := by
                have hcard : Nat.card ↥P * Nat.card ↥H = Nat.card X := hHc.card_mul_card
                have hidx : Nat.card ↥P * P.index = Nat.card X := by
                  rw [mul_comm, Subgroup.index_mul_card]
                have hpos : 0 < Nat.card ↥P := Nat.card_pos
                have hHP : Nat.card ↥H = Nat.card (X ⧸ P) := by
                  rw [Subgroup.index_eq_card] at hidx
                  exact Nat.mul_left_cancel hpos (hcard.trans hidx.symm)
                rw [hHP]
                rw [hZP] at hpp
                exact hpp
              have hle : H ≤ ⊥ := (le_piCore hHnorm hHpi).trans (le_of_eq hcore)
              exact hHne (le_bot_iff.mp hle)
          · -- Case `N ≠ X`: apply the induction hypothesis to `N`
            have hNlt : Nat.card ↥N < Nat.card X := by
              have hle : Nat.card ↥N ≤ Nat.card X := by
                have h := Subgroup.card_le_of_le (le_top : N ≤ ⊤)
                rwa [Subgroup.card_top] at h
              refine lt_of_le_of_ne hle ?_
              intro hEq
              exact hNX (Subgroup.eq_of_le_of_card_ge le_top (by rw [Subgroup.card_top, hEq]))
            have hNle_n : Nat.card ↥N ≤ n := by
              rw [hXcard] at hNlt
              exact Nat.lt_succ_iff.mp hNlt
            have hNps : IsPSolvable p ↥N := isPSolvable_subgroup p X N
            have hNcore : pPrimeCore p ↥N = ⊥ := by
              have hchar : (pPrimeCore p ↥N).Characteristic := pPrimeCore_characteristic p ↥N
              have hnormX : ((pPrimeCore p ↥N).map N.subtype).Normal :=
                map_characteristic_normal hNnorm hchar
              have hpi : IsPiNat (fun r => r ≠ p)
                  (Nat.card ↥((pPrimeCore p ↥N).map N.subtype)) := by
                rw [Subgroup.card_map_of_injective N.subtype_injective]
                exact piCore_isPiNat ↥N (fun q => q ≠ p)
              have hle : (pPrimeCore p ↥N).map N.subtype ≤ ⊥ :=
                (le_piCore hnormX hpi).trans (le_of_eq hcore)
              have hbot := (Subgroup.map_eq_bot_iff (pPrimeCore p ↥N)).mp (le_bot_iff.mp hle)
              rw [Subgroup.ker_subtype] at hbot
              exact le_bot_iff.mp hbot
            have hIH := ih ↥N hNle_n hNps hNcore
            have hZnil : ⁅Z, N⁆ = ⊥ := hZcent hN_le_C
            have hZNcent : Z ≤ Subgroup.centralizer (N : Set X) :=
              Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZnil
            -- `N` is `p`-solvable with `O_{p'}(N) = 1`, so the induction hypothesis applies
            by_cases hcomm : IsMulCommutative ↥Nb
            · -- Case (a): `N̄` abelian, so `N` is nilpotent, whence `N ≤ F(X) = P`
              have hderiv_le : ⁅N, N⁆ ≤ Z := by
                have hm : (⁅N, N⁆).map q = ⊥ := by
                  rw [Subgroup.map_commutator, hN_map,
                    (Subgroup.commutator_self_eq_bot_iff (H := Nb)).mpr hcomm]
                have h' : ⁅N, N⁆ ≤ q.ker := (Subgroup.map_eq_bot_iff ⁅N, N⁆).mp hm
                rwa [hkerq] at h'
              have hnil : Group.IsNilpotent ↥N := by
                apply isNilpotent_of_commutator_le_center
                have htop : (⊤ : Subgroup ↥N).map N.subtype = N := by
                  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
                have h1 : (⁅(⊤ : Subgroup ↥N), (⊤ : Subgroup ↥N)⁆).map N.subtype =
                    ⁅N, N⁆ := by
                  rw [Subgroup.map_commutator, htop]
                have h2 : ⁅(⊤ : Subgroup ↥N), (⊤ : Subgroup ↥N)⁆ ≤ Z.subgroupOf N := by
                  rw [← Subgroup.comap_subtype Z N]
                  exact (Subgroup.map_le_iff_le_comap).mp (by rw [h1]; exact hderiv_le)
                have h3 : Z.subgroupOf N ≤ Subgroup.center ↥N := by
                  intro z hz
                  rw [Subgroup.mem_center_iff]
                  intro w
                  apply Subtype.ext
                  simp only [Subgroup.coe_mul]
                  exact Subgroup.mem_centralizer_iff.mp
                    (hZNcent (Subgroup.mem_subgroupOf.mp hz)) (N.subtype w) w.2
                exact h2.trans h3
              have hNleP : N ≤ P := by
                have h := le_fitting hNnorm hnil
                rwa [fitting_eq_pCore_of_pPrimeCore_eq_bot p X hp hcore] at h
              exact hN_ne_Z (le_antisymm (le_inf hN_le_C hNleP) hZ_le_N)
            · -- Case (b): `N̄` is a non-abelian `p'`-group, and `O_p(N) = Z`
              have hNbp' : IsPiNat (fun r => r ≠ p) (Nat.card ↥Nb) := by
                rcases isMinimalNormal_isPGroup_or_pPrime p (X ⧸ Z) hNbmin with h | h
                · exact absurd (isMinimalNormal_isPGroup_commutative p (X ⧸ Z) hp hNbmin
                    ((isPiNat_prime_iff_isPGroup hp Nb).mp h)) hcomm
                · exact h
              have hcardZ' : Nat.card ↥(Z.subgroupOf N) = Nat.card ↥Z :=
                Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ_le_N).toEquiv
              -- the quotient `↥N ⧸ Z` has order `|N̄|`
              have hquot : Nat.card (↥N ⧸ Z.subgroupOf N) = Nat.card ↥Nb := by
                have h1 : Nat.card ↥N =
                    Nat.card (↥N ⧸ Z.subgroupOf N) * Nat.card ↥(Z.subgroupOf N) :=
                  Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf N)
                rw [hcardZ'] at h1
                refine Nat.mul_right_cancel (Nat.card_pos (α := ↥Z)) ?_
                rw [← h1, hcardN, Nat.mul_comm]
              -- hence `Z` is the Sylow `p`-subgroup of `N`
              have hpcoreN : pCore p ↥N = Z.subgroupOf N := by
                rw [pCore, piCore]
                refine le_antisymm ?_ (le_piCore (hZnorm.subgroupOf N) ?_)
                · refine sSup_le ?_
                  intro H hH
                  rw [mem_piCoreSet] at hH
                  obtain ⟨hHnorm, hHpi⟩ := hH
                  haveI := hHnorm
                  haveI : (Z.subgroupOf N).Normal := hZnorm.subgroupOf N
                  let ρ : ↥N →* ↥N ⧸ (Z.subgroupOf N) := QuotientGroup.mk' (Z.subgroupOf N)
                  have hHmap : Nat.card ↥(H.map ρ) = 1 := by
                    obtain ⟨a, ha⟩ := (isPiNat_prime_iff hp).mp hHpi
                    have h1 : Nat.card ↥(H.map ρ) ∣ p ^ a := by
                      rw [← ha]
                      exact Subgroup.card_map_dvd H ρ
                    have h2 : Nat.card ↥(H.map ρ) ∣ Nat.card ↥Nb := by
                      rw [← hquot]
                      exact Subgroup.card_subgroup_dvd_card _
                    have h3 : Nat.Coprime (p ^ a) (Nat.card ↥Nb) := by
                      refine Nat.Coprime.pow_left _ ?_
                      rw [Nat.Prime.coprime_iff_not_dvd hp]
                      intro hdvd
                      exact hNbp' p hp hdvd rfl
                    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 h3) h2
                  have hle : H.map ρ = ⊥ := by
                    rw [← Subgroup.card_eq_one]
                    exact hHmap
                  have hker := (Subgroup.map_eq_bot_iff H).mp hle
                  rwa [QuotientGroup.ker_mk'] at hker
                · rw [hcardZ']
                  exact isPiNat_of_dvd (Subgroup.card_dvd_of_le hZleP)
                    ((isPiNat_prime_iff_isPGroup hp P).mpr (isPGroup_pCore hp))
              have hcenter' : (⊤ : Subgroup ↥N) ≤
                  Subgroup.centralizer (((Z.subgroupOf N) : Subgroup ↥N) : Set ↥N) := by
                intro w _
                rw [Subgroup.mem_centralizer_iff]
                intro z hz
                apply Subtype.ext
                simp only [Subgroup.coe_mul]
                exact (Subgroup.mem_centralizer_iff.mp
                  (hZNcent (Subgroup.mem_subgroupOf.mp hz)) (N.subtype w) w.2).symm
              rw [hpcoreN] at hIH
              have hNZ' : (⊤ : Subgroup ↥N) ≤ Z.subgroupOf N := hcenter'.trans hIH
              have hNZ : N ≤ Z := by
                intro x hx
                have hx' : (⟨x, hx⟩ : ↥N) ∈ Z.subgroupOf N := hNZ' (Subgroup.mem_top _)
                rwa [Subgroup.mem_subgroupOf] at hx'
              exact hN_ne_Z (le_antisymm hNZ hZ_le_N)

/-- If `X` is a finite `p`-solvable group with `O_{p'}(X) = 1` then `C_X(O_p(X)) ≤ O_p(X)`. -/
theorem centralizer_pCore_le_of_pPrimeCore_eq_bot (p : ℕ) (X : Type*) [Group X] [Finite X]
    (hp : p.Prime) [IsPSolvable p X] (hcore : pPrimeCore p X = ⊥) :
    Subgroup.centralizer ((pCore p X : Subgroup X) : Set X) ≤ pCore p X :=
  centralizer_pCore_le_aux p hp (Nat.card X) X le_rfl ‹IsPSolvable p X› hcore

theorem centralizer_pPrimePCore_le (p : ℕ) (G : Type*) [Group G] [Finite G] [Work.Fitting.IsPSolvable p G] :
    Work.Fitting.sectionCentralizer (Work.Fitting.pPrimeCore p G) (Work.Fitting.pPrimePCore p G) ≤
      Work.Fitting.pPrimePCore p G := by
  by_cases hp : p.Prime
  · haveI : Fact p.Prime := ⟨hp⟩
    haveI : Finite (G ⧸ pPrimeCore p G) :=
      Finite.of_surjective _ (QuotientGroup.mk'_surjective (pPrimeCore p G))
    haveI : IsPSolvable p (G ⧸ pPrimeCore p G) := isPSolvable_quotient p G (pPrimeCore p G)
    have hcore : pPrimeCore p (G ⧸ pPrimeCore p G) = ⊥ :=
      piCore_quotient_eq_bot (fun q => q ≠ p) G
    have hkey := centralizer_pCore_le_of_pPrimeCore_eq_bot p (G ⧸ pPrimeCore p G) hp hcore
    have hmap : (pPrimePCore p G).map (QuotientGroup.mk' (pPrimeCore p G)) =
        pCore p (G ⧸ pPrimeCore p G) :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
    have hsc : sectionCentralizer (pPrimeCore p G) (pPrimePCore p G) =
        (Subgroup.centralizer
          ((pCore p (G ⧸ pPrimeCore p G) : Subgroup (G ⧸ pPrimeCore p G)) :
            Set (G ⧸ pPrimeCore p G))).comap (QuotientGroup.mk' (pPrimeCore p G)) := by
      rw [sectionCentralizer, hmap]
    rw [hsc]
    exact (Subgroup.comap_mono hkey).trans (le_of_eq rfl)
  · have hH : pPrimeCore p G = ⊤ := pPrimeCore_eq_top_of_not_prime p G hp
    have hK : pPrimePCore p G = ⊤ := pPrimePCore_eq_top_of_pPrimeCore_eq_top p G hH
    exact le_top.trans (le_of_eq hK.symm)

end Work.Fitting
