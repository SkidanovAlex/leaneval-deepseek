import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.L27_two_part_centralized_proved
import Submission.Work.CORE2B.L27_two_part
import Submission.Work.CORE2B.sylow_central_of_large_inter
import Submission.Work.CORE2B.L27cf_twoResidual
import Submission.Work.CORE2B.t_central_in_S
import Submission.Work.CORE2B.BenderCtx_sylow_not_cyclic
import Submission.Work.CORE2B.L27cf_helpers
import Submission.Work.BMAX.InvolutionInverts

/-!
# CORE2B — `t` centralizes `F(M)` (Bender 1981, Lemma 2.7, "`[M,t] ⊆ C_M(F(M))`")

Bender's Lemma 2.7 (p. 221) reads: "Our assumptions force every normal subgroup of `M` of order
divisible by `4` to contain `t`. Hence `E(M) = 1` and `t` centralizes `O₂(M)`. Then `t` centralizes
`F_π(M)` and inverts `F_{π'}(M)`, by Lemma 2.3.i/ii and since `t ∈ O₂(Ĥ)`. Now
`[M,t] ⊆ C_M(F(M)) ≤ F(M)` and `M` is solvable."

This file proves the middle step, i.e. the leaf

  `⁅M, zpowers B.t⁆ ≤ C_G(F(M))`    (`F(M) = Work.GW2.fittingIn M`),

for every `M` satisfying `L27Hyp B M`.  The argument is Bender's, written out for an arbitrary
`m ∈ M`: on `F(M)`, conjugation by `⁅m,t⁆ = m t m⁻¹ t⁻¹` is

  `c_{⁅m,t⁆} = c_m ∘ β ∘ c_m⁻¹ ∘ β⁻¹`,   `β = c_t|_{F(M)}`,

and each `c_m` (`m ∈ M`) preserves the characteristic pieces of the nilpotent group `F(M)`.
`β` is trivial on `O₂(F(M))` (Bender's step 1, the leaf `L27_two_part_centralized`) and inverts
`O_{π'}(F(M))` (Lemma 2.3.ii, `L27cf_inverts_fittingPiIn_pi_compl`).  On the remaining piece
`O_{π ∩ {2}ᶜ}(F(M))` — the odd part of the `π`-part — `β` is trivial as well: that piece lies in
`F_π(M) ≤ Ĥ` (Lemma 2.3.i) while `t ∈ O₂(Ĥ) ◁ Ĥ`, so `[x,t] ∈ O₂(Ĥ) ∩ O_{π ∩ {2}ᶜ}(F(M))`, the
intersection of a `2`-group with a group of odd order.  Being trivial on each of the three pieces
(which generate `F(M)`, by the nilpotent `π`-decomposition), `c_{⁅m,t⁆}` is the identity on
`F(M)`, i.e. `⁅m,t⁆` centralizes `F(M)`.

A colleague's module `Submission.Work.CORE2B.L27cf_fittingIn_le_sup_three` proves the same
three-set nilpotent splitting (§3 below) in the form of an inclusion; the version here is
self-contained so that the leaf does not depend on a module that is still being developed.
-/

open scoped MatrixGroups commutatorElement

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 0. Bender's step 1: `t` centralizes `F₂(M)`

Bender's first step is "`t` centralizes `O₂(M)`".  `F₂(M) = O₂(F(M)) ≤ O₂(M)`, and a normal
`2`-subgroup of `M` lies in every Sylow `2`-subgroup of `M`, so it suffices that `t` is
`2`-central in `M`: that some Sylow `2`-subgroup of `M` commutes with `t`.  This is provided by
`L27Hyp.size`'s three alternatives — `8 ≤ |S ⊓ M|` (`sylow_central_of_large_inter`), `|S| = 4`
(`L27two.sylow_central_of_card_four`) and `t ∈ O²(M)` (`L27cf_twoResidual`, Thompson's transfer
lemma).

(The leaf `L27_two_part_centralized` is assembled in the same way in
`L27_two_part_centralized_proved`; the version below is recorded here so that the present file
does not depend on that module's unfinished third case.) -/

/-- `F₂(M) = O₂(F(M)) ≤ O₂(M)` (in the ambient group). -/
theorem L27cff_fittingPiIn_two_le_pCoreIn_two {G : Type} [Group G] [Finite G] (M : Subgroup G) :
    Work.GW2.fittingPiIn ({n : ℕ | n = 2}) M ≤ Work.GW2.pCoreIn 2 M := by
  have h := Subgroup.map_mono (f := M.subtype) (L27c_fittingPi_two_le_pCore_two (M := ↥M))
  simpa only [Work.GW2.fittingPiIn, Work.GW2.pCoreIn] using h

/-- **Bender 1981, Lemma 2.7, step 1**: `t` centralizes `F₂(M)`. -/
theorem L27cff_two_part_centralized : Work.CORE2B.L27_two_part_centralized := by
  intro T h23 h26 G _ _ hFT hCtx B M hM
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hncS : ¬ IsCyclic ↥(B.S : Subgroup G) := BenderCtx_sylow_not_cyclic hCtx B.S
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Nonempty (↥(B.S : Subgroup G) ≃* DihedralGroup n) := by
    rcases hCtx.sylow B.S with h | h
    · exact absurd h hncS
    · exact h
  have htc : ∀ x ∈ (B.S : Subgroup G), x * B.t = B.t * x := t_central_in_S B
  have key : ∀ P : Sylow 2 M, (∀ x ∈ (P : Subgroup M), (x : G) * B.t = B.t * (x : G)) →
      Work.GW2.fittingPiIn ({2} : Set ℕ) M ≤ Subgroup.centralizer ({B.t} : Set G) :=
    fun P hP => (L27cff_fittingPiIn_two_le_pCoreIn_two M).trans
      (L27c_pCoreIn_two_le_centralizer_of_sylow M B.t P hP)
  rcases hM.size with h8 | h4 | hres
  · obtain ⟨P, hP⟩ := sylow_central_of_large_inter B.S n hn B.t B.t_order htc M hM.t_mem
      hM.sylow_nc h8
    exact key P hP
  · obtain ⟨P, hP⟩ := L27two.sylow_central_of_card_four B.S B.t B.t_order h4 M hM.t_mem
      hM.sylow_nc
    exact key P hP
  · obtain ⟨P, hP⟩ := L27cf_twoResidual B.S n hn B.t B.t_order htc M hM.t_mem
      hM.sylow_nc hres
    exact key P hP

/-! ## 1. Two elementary commutator computations

If `t` is an involution normalizing `F` and acting on `F` trivially (resp. by inversion), then
`⁅M,t⁆` centralizes `F`: conjugation by `⁅m,t⁆ = m t m⁻¹ t⁻¹` is the commutator `c_m c_t c_m⁻¹ c_t`
in `Aut(F)`, and either action of `t` makes this trivial on `F`.

(Reproofs of `Work.CORE2B.commutator_le_centralizer_of_centralizes` and `…_of_inverts` of
`L27_crux_commutator_2prime`, a module whose dependency `L27_api` does not currently compile.) -/

/-- If `t` centralizes `F` pointwise (and `t² = 1`), then `⁅M,t⁆` centralizes `F`. -/
theorem L27cf_comm_le_centralizer_of_centralizes {G : Type} [Group G] {M F : Subgroup G} {t : G}
    (hM : M ≤ Subgroup.normalizer (F : Set G))
    (hcen : ∀ x ∈ F, t * x * t⁻¹ = x) (ht : t * t = 1) :
    ⁅M, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer (F : Set G) := by
  have hpow : ∀ y ∈ Subgroup.zpowers t, y = 1 ∨ y = t := by
    intro y hy
    rw [Subgroup.zpowers_eq_closure] at hy
    revert hy
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact Or.inr hx
    · exact Or.inl rfl
    · intro x y _ _ hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Or.inl (by rw [hx, hy, mul_one])
      · exact Or.inr (by rw [hx, hy, one_mul])
      · exact Or.inr (by rw [hx, hy, mul_one])
      · exact Or.inl (by rw [hx, hy]; exact ht)
    · intro x _ hx
      rcases hx with hx | hx
      · exact Or.inl (by rw [hx]; exact inv_one)
      · exact Or.inr (by rw [hx]; exact inv_eq_of_mul_eq_one_right ht)
  have hone : ∀ m ∈ M, ⁅m, (1 : G)⁆ ∈ Subgroup.centralizer (F : Set G) := by
    intro m _
    rw [commutatorElement_one_right]
    exact Subgroup.one_mem _
  have hgen : ∀ m ∈ M, ⁅m, t⁆ ∈ Subgroup.centralizer (F : Set G) := by
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have key1 : t⁻¹ * z * t = z := by
      simpa [htinv] using hcen z hz
    have hmemF : m⁻¹ * z * m ∈ F := by
      have h := (Subgroup.mem_normalizer_iff.mp (hM (M.inv_mem hm)) z).mp hz
      simpa using h
    have key2 : t * (m⁻¹ * z * m) * t⁻¹ = m⁻¹ * z * m := hcen _ hmemF
    have hconj : ⁅m, t⁆ * z * ⁅m, t⁆⁻¹ = z := by
      calc ⁅m, t⁆ * z * ⁅m, t⁆⁻¹
          = m * (t * (m⁻¹ * (t⁻¹ * z * t) * m) * t⁻¹) * m⁻¹ := by
            rw [commutatorElement_def]; group
        _ = m * (t * (m⁻¹ * z * m) * t⁻¹) * m⁻¹ := by rw [key1]
        _ = m * (m⁻¹ * z * m) * m⁻¹ := by rw [key2]
        _ = z := by group
    have h1 : ⁅m, t⁆ * z = z * ⁅m, t⁆ := by
      calc ⁅m, t⁆ * z = (⁅m, t⁆ * z * ⁅m, t⁆⁻¹) * ⁅m, t⁆ := by group
        _ = z * ⁅m, t⁆ := by rw [hconj]
    exact h1.symm
  rw [Subgroup.commutator_le]
  intro m hm y hy
  rcases hpow y hy with rfl | rfl
  · exact hone m hm
  · exact hgen m hm

/-- If `t` inverts `F` pointwise (and `t² = 1`), then `⁅M,t⁆` centralizes `F`. -/
theorem L27cf_comm_le_centralizer_of_inverts {G : Type} [Group G] {M F : Subgroup G} {t : G}
    (hM : M ≤ Subgroup.normalizer (F : Set G))
    (hinv : ∀ x ∈ F, t * x * t⁻¹ = x⁻¹) (ht : t * t = 1) :
    ⁅M, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer (F : Set G) := by
  have hpow : ∀ y ∈ Subgroup.zpowers t, y = 1 ∨ y = t := by
    intro y hy
    rw [Subgroup.zpowers_eq_closure] at hy
    revert hy
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact Or.inr hx
    · exact Or.inl rfl
    · intro x y _ _ hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Or.inl (by rw [hx, hy, mul_one])
      · exact Or.inr (by rw [hx, hy, one_mul])
      · exact Or.inr (by rw [hx, hy, mul_one])
      · exact Or.inl (by rw [hx, hy]; exact ht)
    · intro x _ hx
      rcases hx with hx | hx
      · exact Or.inl (by rw [hx]; exact inv_one)
      · exact Or.inr (by rw [hx]; exact inv_eq_of_mul_eq_one_right ht)
  have hone : ∀ m ∈ M, ⁅m, (1 : G)⁆ ∈ Subgroup.centralizer (F : Set G) := by
    intro m _
    rw [commutatorElement_one_right]
    exact Subgroup.one_mem _
  have hgen : ∀ m ∈ M, ⁅m, t⁆ ∈ Subgroup.centralizer (F : Set G) := by
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have hzF : m * z⁻¹ * m⁻¹ ∈ F := by
      have h : m * z⁻¹ * m⁻¹ = (m * z * m⁻¹)⁻¹ := by group
      rw [h]
      exact F.inv_mem ((Subgroup.mem_normalizer_iff.mp (hM hm) z).mp hz)
    have key1 : t⁻¹ * z * t = z⁻¹ := by
      rw [htinv]
      simpa [htinv] using hinv z hz
    have hmemF : m⁻¹ * z⁻¹ * m ∈ F := by
      have h := (Subgroup.mem_normalizer_iff.mp (hM (M.inv_mem hm)) z⁻¹).mp (F.inv_mem hz)
      simpa using h
    have key2 : t * (m⁻¹ * z⁻¹ * m) * t⁻¹ = m⁻¹ * z * m := by
      have h := hinv (m⁻¹ * z⁻¹ * m) hmemF
      rw [h]
      group
    have hconj : ⁅m, t⁆ * z * ⁅m, t⁆⁻¹ = z := by
      calc ⁅m, t⁆ * z * ⁅m, t⁆⁻¹
          = m * (t * (m⁻¹ * (t⁻¹ * z * t) * m) * t⁻¹) * m⁻¹ := by
            rw [commutatorElement_def]; group
        _ = m * (t * (m⁻¹ * z⁻¹ * m) * t⁻¹) * m⁻¹ := by rw [key1]
        _ = m * (m⁻¹ * z * m) * m⁻¹ := by rw [key2]
        _ = z := by group
    have h1 : ⁅m, t⁆ * z = z * ⁅m, t⁆ := by
      calc ⁅m, t⁆ * z = (⁅m, t⁆ * z * ⁅m, t⁆⁻¹) * ⁅m, t⁆ := by group
        _ = z * ⁅m, t⁆ := by rw [hconj]
    exact h1.symm
  rw [Subgroup.commutator_le]
  intro m hm y hy
  rcases hpow y hy with rfl | rfl
  · exact hone m hm
  · exact hgen m hm

/-- `t * x = x * t` together with `t * t = 1` gives `t * x * t⁻¹ = x`. -/
theorem L27cf_conj_eq_of_commute {G : Type} [Group G] {t x : G} (ht : t * t = 1)
    (h : t * x = x * t) : t * x * t⁻¹ = x := by
  rw [inv_eq_of_mul_eq_one_right ht, h, mul_assoc, ht, mul_one]

/-! ## 2. Assembly: trivial/inverting action on three generating pieces -/

/-- If `M` normalizes `A`, `B` and `C`, the involution `t` centralizes `A` and `B` and inverts
`C`, then `⁅M,t⁆` centralizes `A ⊔ B ⊔ C`. -/
theorem L27cf_comm_le_centralizer_of_three {G : Type} [Group G] {M A B C : Subgroup G} {t : G}
    (hMA : M ≤ Subgroup.normalizer (A : Set G))
    (hMB : M ≤ Subgroup.normalizer (B : Set G))
    (hMC : M ≤ Subgroup.normalizer (C : Set G))
    (hAcen : ∀ x ∈ A, t * x * t⁻¹ = x) (hBcen : ∀ x ∈ B, t * x * t⁻¹ = x)
    (hCinv : ∀ x ∈ C, t * x * t⁻¹ = x⁻¹) (ht : t * t = 1) :
    ⁅M, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer ((A ⊔ B ⊔ C : Subgroup G) : Set G) := by
  have hCA := L27cf_comm_le_centralizer_of_centralizes (M := M) (F := A) hMA hAcen ht
  have hCB := L27cf_comm_le_centralizer_of_centralizes (M := M) (F := B) hMB hBcen ht
  have hCC := L27cf_comm_le_centralizer_of_inverts (M := M) (F := C) hMC hCinv ht
  rw [Subgroup.commutator_le]
  intro m hm y hy
  have hmem : ⁅m, y⁆ ∈ ⁅M, Subgroup.zpowers t⁆ :=
    Subgroup.commutator_mem_commutator hm hy
  have hA : A ≤ Subgroup.centralizer ({⁅m, y⁆} : Set G) := by
    intro a ha
    refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
    rw [Set.mem_singleton_iff] at hk
    subst hk
    exact (Subgroup.mem_centralizer_iff.mp (hCA hmem) a ha).symm
  have hB : B ≤ Subgroup.centralizer ({⁅m, y⁆} : Set G) := by
    intro b hb
    refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
    rw [Set.mem_singleton_iff] at hk
    subst hk
    exact (Subgroup.mem_centralizer_iff.mp (hCB hmem) b hb).symm
  have hC : C ≤ Subgroup.centralizer ({⁅m, y⁆} : Set G) := by
    intro c hc
    refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
    rw [Set.mem_singleton_iff] at hk
    subst hk
    exact (Subgroup.mem_centralizer_iff.mp (hCC hmem) c hc).symm
  have hsup : A ⊔ B ⊔ C ≤ Subgroup.centralizer ({⁅m, y⁆} : Set G) :=
    sup_le (sup_le hA hB) hC
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  exact (Subgroup.mem_centralizer_iff.mp (hsup hf) ⁅m, y⁆ rfl).symm

/-! ## 3. The nilpotent `π`-decomposition of `F(K)`

A finite nilpotent group is the join of its (normal) Sylow subgroups, and each Sylow `q`-subgroup
lies in `O_{π_i}` as soon as `q ∈ π_i`; so three `π`-cores covering the primes generate all of it.
-/

/-- **Universal property of `O_π`.**  A normal `π`-subgroup lies in `O_π(G)`. -/
theorem L27cff_le_piCore_of_normal_isPiSubgroup {G : Type} [Group G] {π : Set ℕ}
    {N : Subgroup G} [N.Normal] (hN : Subgroup.IsPiSubgroup π N) :
    N ≤ Work.GW2.piCore π G :=
  Subgroup.normal_le_normalCore.mpr (le_sSup ⟨‹N.Normal›, hN⟩)

/-- **A finite nilpotent group is generated by three `π`-cores**, as soon as the `πᵢ` cover the
primes. -/
theorem L27cff_piCore_sup_three_eq_top {H : Type} [Group H] [Finite H] [Group.IsNilpotent H]
    (π₁ π₂ π₃ : Set ℕ)
    (hcover : ∀ q : ℕ, q.Prime → q ∈ π₁ ∨ q ∈ π₂ ∨ q ∈ π₃) :
    Work.GW2.piCore π₁ H ⊔ Work.GW2.piCore π₂ H ⊔ Work.GW2.piCore π₃ H = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← OddOrder.Isaacs.Ch01.iSup_default_sylow_eq_top_of_nilpotent H]
  refine iSup_le ?_
  rintro ⟨p, hp⟩
  have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp
  haveI : Fact p.Prime := ⟨hpP⟩
  haveI hQn : ((default : Sylow p H) : Subgroup H).Normal :=
    OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent (default : Sylow p H)
  have hQg : IsPGroup p ((default : Sylow p H) : Subgroup H) :=
    (default : Sylow p H).isPGroup'
  rcases hcover p hpP with hp1 | hp2 | hp3
  · exact ((L27cff_le_piCore_of_normal_isPiSubgroup (G := H)
      (Subgroup.isPiSubgroup_of_isPGroup_of_mem hQg hp1)).trans le_sup_left).trans le_sup_left
  · exact ((L27cff_le_piCore_of_normal_isPiSubgroup (G := H)
      (Subgroup.isPiSubgroup_of_isPGroup_of_mem hQg hp2)).trans le_sup_right).trans le_sup_left
  · exact (L27cff_le_piCore_of_normal_isPiSubgroup (G := H)
      (Subgroup.isPiSubgroup_of_isPGroup_of_mem hQg hp3)).trans le_sup_right

/-- **`F(K)` is generated by its three `π`-parts** whenever the `πᵢ` cover the primes. -/
theorem L27cff_fittingPiIn_sup_three_eq_fittingIn {G : Type} [Group G] [Finite G]
    (K : Subgroup G) {π₁ π₂ π₃ : Set ℕ}
    (hcover : ∀ q : ℕ, q.Prime → q ∈ π₁ ∨ q ∈ π₂ ∨ q ∈ π₃) :
    Work.GW2.fittingPiIn π₁ K ⊔ Work.GW2.fittingPiIn π₂ K ⊔ Work.GW2.fittingPiIn π₃ K
      = Work.GW2.fittingIn K := by
  haveI : Group.IsNilpotent ↥(Work.GW2.fitting ↥K) := L27cf_isNilpotent_fitting
  have key : Work.GW2.fittingPi π₁ ↥K ⊔ Work.GW2.fittingPi π₂ ↥K ⊔ Work.GW2.fittingPi π₃ ↥K
      = Work.GW2.fitting ↥K := by
    unfold Work.GW2.fittingPi
    rw [← Subgroup.map_sup, ← Subgroup.map_sup,
      L27cff_piCore_sup_three_eq_top π₁ π₂ π₃ hcover,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  unfold Work.GW2.fittingPiIn Work.GW2.fittingIn
  rw [← Subgroup.map_sup, ← Subgroup.map_sup, key]

/-- The inclusion form of the three-piece nilpotent splitting of `F(K)`. -/
theorem L27cff_fittingIn_le_sup_three {G : Type} [Group G] [Finite G] (K : Subgroup G)
    {π₁ π₂ π₃ : Set ℕ} (hcover : ∀ q : ℕ, q.Prime → q ∈ π₁ ∨ q ∈ π₂ ∨ q ∈ π₃) :
    Work.GW2.fittingIn K ≤
      Work.GW2.fittingPiIn π₁ K ⊔ Work.GW2.fittingPiIn π₂ K ⊔ Work.GW2.fittingPiIn π₃ K :=
  le_of_eq (L27cff_fittingPiIn_sup_three_eq_fittingIn K hcover).symm

/-! ## 4. `O₂(Ĥ)` is a `2`-group; `F_σ(M)` is a `σ`-group -/

/-- `O₂(Ĥ) = O₂(↥Ĥ)`, viewed in `G`, is a `2`-group (it is the image of `O₂(↥Ĥ)` under the
injective inclusion `↥Ĥ ↪ G`). -/
theorem L27cff_isPGroup_pCoreIn_two {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    IsPGroup 2 (Work.GW2.pCoreIn 2 K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (L27c_pCore_isPGroup (G := ↥K) (p := 2))
  rw [Work.GW2.pCoreIn]
  refine IsPGroup.of_card (n := n) ?_
  rw [Subgroup.card_map_of_injective K.subtype_injective]
  exact hn

/-- `F_σ(K) = O_σ(F(K))` is a `σ`-subgroup of `G`. -/
theorem L27cff_isPiSubgroup_fittingPiIn {G : Type} [Group G] [Finite G] (π : Set ℕ)
    (K : Subgroup G) : Subgroup.IsPiSubgroup π (Work.GW2.fittingPiIn π K) := by
  have h := OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := ↥(Work.GW2.fitting ↥K)) π
  rw [Work.GW2.fittingPiIn, Work.GW2.fittingPi, piCore_eq_oPiCore_local]
  intro q hq
  rw [Subgroup.card_map_of_injective K.subtype_injective,
    Subgroup.card_map_of_injective (Work.GW2.fitting ↥K).subtype_injective] at hq
  exact h q hq

/-- If `σ` avoids the prime `2` then `F_σ(K)` has odd order. -/
theorem L27cff_odd_card_fittingPiIn_of_subset_compl {G : Type} [Group G] [Finite G]
    {σ : Set ℕ} (hσ : σ ⊆ ({2}ᶜ : Set ℕ)) (K : Subgroup G) :
    Odd (Nat.card (Work.GW2.fittingPiIn σ K)) :=
  L27cf_odd_card_of_isPiSubgroup hσ (L27cff_isPiSubgroup_fittingPiIn σ K)

/-! ## 5. `t` centralizes the odd part `O_{π ∩ {2}ᶜ}(F(M))` of the `π`-part of `F(M)`

This is Bender's "`t` centralizes `F_π(M)`, by Lemma 2.3.i … and since `t ∈ O₂(Ĥ)`", for the odd
part: `x ∈ O_{π ∩ {2}ᶜ}(F(M)) ⊆ F_π(M) ≤ Ĥ`, and `t ∈ O₂(Ĥ) ◁ Ĥ`, so
`⁅x,t⁆ ∈ O₂(Ĥ)` (a `2`-group); on the other hand `⁅x,t⁆ ∈ O_{π ∩ {2}ᶜ}(F(M))` (odd order).  If
`F*(Ĥ)` is a `p`-group then `p = 2`, `π = {2}` and `O_{π ∩ {2}ᶜ}(F(M)) = 1`. -/

/-- **Bender 1981, Lemma 2.7, step "`t` centralizes `F_π(M)`", odd part.** -/
theorem L27cff_centralizes_odd_pi_part :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), Work.CORE2B.L27Hyp B M →
      Work.GW2.Lemma23Prop → Work.GW2.Thm26Prop →
        Work.GW2.fittingPiIn (B.pi ∩ ({2}ᶜ : Set ℕ)) M ≤
          Subgroup.centralizer ({B.t} : Set G) := by
  intro G _ _ hFT hCtx B M hD h23 h26 x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  by_cases hpg : ∃ p : ℕ, p.Prime ∧ IsPGroup p (Work.GW2.fstarIn B.Hhat)
  · -- `F*(Ĥ)` is a `p`-group: then `π = {2}` and there is nothing to prove
    have hbot := L27cf_fittingPiIn_inter_compl_eq_bot h26 hFT hCtx B hpg M
    rw [hbot] at hx
    rw [Subgroup.mem_bot.mp hx]
    simp
  · -- `F*(Ĥ)` is not a `p`-group: Lemma 2.3.i and `t ∈ O₂(Ĥ)`
    have hle : Work.GW2.fittingPiIn B.pi M ≤ B.Hhat :=
      (h23 G hFT hCtx B M hD.M_ne_top hD.rel).1 hpg
    have hxH : x ∈ B.Hhat := hle (fittingPiIn_mono' Set.inter_subset_left M hx)
    have ht : B.t ∈ Work.GW2.pCoreIn 2 B.Hhat := L27cf_t_mem_pCoreIn_two h26 hFT hCtx B
    have hN : B.Hhat ≤
        Subgroup.normalizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) :=
      L27cf_le_normalizer_pCoreIn_two B.Hhat
    have hconj : x * B.t * x⁻¹ ∈ Work.GW2.pCoreIn 2 B.Hhat :=
      (Subgroup.mem_normalizer_iff.mp (hN hxH) B.t).mp ht
    -- `⁅x,t⁆` lies in the `2`-group `O₂(Ĥ)`
    have hyO : ⁅x, B.t⁆ ∈ Work.GW2.pCoreIn 2 B.Hhat := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ ht)
    -- `⁅x,t⁆` lies in `O_{π ∩ {2}ᶜ}(F(M))`
    have htN : B.t ∈ Subgroup.normalizer
        ((Work.GW2.fittingPiIn (B.pi ∩ ({2}ᶜ : Set ℕ)) M : Subgroup G) : Set G) :=
      le_normalizer_fittingPiIn_local (B.pi ∩ ({2}ᶜ : Set ℕ)) M hD.t_mem
    have hyσ : ⁅x, B.t⁆ ∈ Work.GW2.fittingPiIn (B.pi ∩ ({2}ᶜ : Set ℕ)) M := by
      have h1 : B.t * x * B.t⁻¹ ∈ Work.GW2.fittingPiIn (B.pi ∩ ({2}ᶜ : Set ℕ)) M :=
        (Subgroup.mem_normalizer_iff.mp htN x).mp hx
      have hid : ⁅x, B.t⁆ = x * (B.t * x * B.t⁻¹)⁻¹ := by
        rw [commutatorElement_def]; group
      rw [hid]
      exact Subgroup.mul_mem _ hx (Subgroup.inv_mem _ h1)
    -- a `2`-group meets a subgroup of odd order trivially
    have hoddK : Odd (Nat.card (Work.GW2.fittingPiIn (B.pi ∩ ({2}ᶜ : Set ℕ)) M)) :=
      L27cff_odd_card_fittingPiIn_of_subset_compl Set.inter_subset_right M
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (L27cff_isPGroup_pCoreIn_two (K := B.Hhat))
    have hdvd : orderOf ⁅x, B.t⁆ ∣ 2 ^ n := by
      rw [← hn]
      exact Subgroup.orderOf_dvd_natCard _ hyO
    have hodd_y : Odd (orderOf ⁅x, B.t⁆) :=
      hoddK.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hyσ)
    have hcop : Nat.Coprime (orderOf ⁅x, B.t⁆) (2 ^ n) :=
      (Nat.coprime_two_right.mpr hodd_y).pow_right n
    have hy1 : ⁅x, B.t⁆ = 1 :=
      orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)
    have h2 : x * B.t * x⁻¹ = B.t := by
      have h := hy1
      rw [commutatorElement_def] at h
      have h3 := congrArg (· * B.t) h
      simpa [mul_assoc] using h3
    calc B.t * x = (x * B.t * x⁻¹) * x := by rw [h2]
      _ = x * B.t := by group

/-! ## 6. The target -/

theorem L27_centralizes_fitting_crux :
    ∀ (T : Work.GW2.LocalToolkit) (_h23 : Work.GW2.Lemma23Prop) (_h26 : Work.GW2.Thm26Prop)
      (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), Work.CORE2B.L27Hyp B M →
        ⁅M, Subgroup.zpowers B.t⁆ ≤
          Subgroup.centralizer ((Work.GW2.fittingIn M : Subgroup G) : Set G) := by
  intro T h23 h26 G _ _ hFT hCtx B M hD
  -- `t` is an involution
  have ht2 : B.t * B.t = 1 := by
    have h := pow_orderOf_eq_one B.t
    rw [B.t_order] at h
    simpa [pow_two] using h
  -- **(1)** `t` centralizes `O₂(F(M))` (Bender's step 1).
  have hcen2 : ∀ x ∈ Work.GW2.fittingPiIn ({2} : Set ℕ) M, B.t * x * B.t⁻¹ = x := by
    intro x hx
    exact L27cf_conj_eq_of_commute ht2
      (Subgroup.mem_centralizer_iff.mp
        (L27cff_two_part_centralized T h23 h26 G hFT hCtx B M hD hx) B.t rfl)
  -- **(2)** `t` centralizes the odd part `O_{π ∩ {2}ᶜ}(F(M))` of `F_π(M)` (Lemma 2.3.i).
  have hcenσ : ∀ x ∈ Work.GW2.fittingPiIn (B.pi ∩ ({2}ᶜ : Set ℕ)) M,
      B.t * x * B.t⁻¹ = x := by
    intro x hx
    exact L27cf_conj_eq_of_commute ht2
      (Subgroup.mem_centralizer_iff.mp
        (L27cff_centralizes_odd_pi_part G hFT hCtx B M hD h23 h26 hx) B.t rfl)
  -- **(3)** `t` inverts `O_{π'}(F(M))` (Lemma 2.3.ii).
  have hinvπ : ∀ x ∈ Work.GW2.fittingPiIn B.piᶜ M, B.t * x * B.t⁻¹ = x⁻¹ :=
    L27cf_inverts_fittingPiIn_pi_compl h23 h26 hFT hCtx B M hD
  -- all three pieces are normalized by `M ∋ t`
  have hnorm : ∀ π : Set ℕ, M ≤
      Subgroup.normalizer ((Work.GW2.fittingPiIn π M : Subgroup G) : Set G) :=
    fun π => le_normalizer_fittingPiIn_local π M
  -- **(4)** the three pieces generate `F(M)` (nilpotent `π`-decomposition)
  have hdec : Work.GW2.fittingIn M ≤
      Work.GW2.fittingPiIn ({2} : Set ℕ) M ⊔
        Work.GW2.fittingPiIn (B.pi ∩ ({2}ᶜ : Set ℕ)) M ⊔
          Work.GW2.fittingPiIn B.piᶜ M :=
    L27cff_fittingIn_le_sup_three M (fun q _ => by
      rcases eq_or_ne q 2 with h | h
      · exact Or.inl (by rw [h]; exact Set.mem_singleton 2)
      · by_cases hqπ : q ∈ B.pi
        · exact Or.inr (Or.inl ⟨hqπ, by rw [Set.mem_compl_iff, Set.mem_singleton_iff]; exact h⟩)
        · exact Or.inr (Or.inr (by rw [Set.mem_compl_iff]; exact hqπ)))
  -- **(5)** assembly
  refine (L27cf_comm_le_centralizer_of_three (hnorm {2}) (hnorm (B.pi ∩ ({2}ᶜ : Set ℕ)))
    (hnorm B.piᶜ) hcen2 hcenσ hinvπ ht2).trans ?_
  exact Subgroup.centralizer_le hdec

end Work.CORE2B
