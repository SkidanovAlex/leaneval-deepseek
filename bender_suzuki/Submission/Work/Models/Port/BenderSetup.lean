/-
**The abstract rank-one `(B,N)`-pair of characteristic two (a "Bender group").**

The output of Bender's theorem (1971) for a finite group `G` with a strongly embedded subgroup `M`
is, in the case where the answer is *not* "cyclic or quaternion Sylow `2`-subgroup":

* a Sylow `2`-subgroup `U ≤ M` of `G` with `M = N_G(U)`,
* a complement `T` of `U` in `M` of odd order (`B = M = U ⋊ T`, Schur--Zassenhaus),
* a Weyl element `w ∈ N_G(T) \ B`,
* `G` acting `2`-transitively on `G ⧸ B`, with `U` regular on the non-base points.

`BenderPair` below packages exactly this data.  All the structural consequences a future
application of Suzuki's classification needs are then *derived* from the axioms, mostly by
appealing to the abstract lemmas of the commons (`Commons.GroupTheory.Bender.*`,
`Commons.GroupTheory.BNPair.*` and `Commons.GroupTheory.StronglyEmbedded.*`): the Bender action
(`benderAction`), the regularity of `U` off the base point (`u_free`), `2`-transitivity
(`isMultiplyPretransitive_two`), the Bruhat decomposition `G = B ∪ BwB` (`bruhat`),
`N_G(T) = T⟨w⟩` (`normalizer_T`), the `T`-fixed points (`fixedPoints_eq_base_or_weyl`),
`N_G(U) = B` (`normalizer_U`), `#Syl ₂(G) = [G : B]` (`card_sylow_two`), the order
`|G| = |U|·|T|·(|U|+1)` (`card_eq_card_U_mul_card_T_mul_succ`) and the involution count
(`card_involutions`).
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.Commons.GroupTheory.Bender.isBenderAction_coset
import Submission.Work.Models.Port.Commons.GroupTheory.Bender.eq_of_smul_eq_self_of_mem_of_isPGroup_two
import Submission.Work.Models.Port.Commons.GroupTheory.Bender.card_sylow_two_eq_index_stabilizer_of_isPGroup_of_odd_index
import Submission.Work.Models.Port.Commons.GroupTheory.Bender.existsUnique_fixedPoint_isPGroup_two
import Submission.Work.Models.Port.Commons.GroupTheory.GroupAction.isMultiplyPretransitive_two_of_regular_of_card
import Submission.Work.Models.Port.Commons.GroupTheory.GroupAction.mem_or_mem_mul_mul_of_twoTransitive
import Submission.Work.Models.Port.Commons.GroupTheory.BNPair.normalizer_eq_sup_zpowers
import Submission.Work.Models.Port.Commons.GroupTheory.BNPair.bruhat
import Submission.Work.Models.Port.Commons.GroupTheory.BNPair.unipotent_is_sylow
import Submission.Work.Models.Port.Commons.GroupTheory.BNPair.normalizer_eq_borel
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.stronglyEmbedded_map_of_surjective
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.mem_map_mulAut_conj_iff
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.normalizer_map_mulAut_conj
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.map_inf_eq_of_ker_le
import Submission.Work.Models.Port.Commons.GroupTheory.BNPair.fixedPoints_eq_base_or_weyl
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.normalizer_le_of_isPGroup_le
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.card_involutions_eq_index_mul
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.card_sup_of_inf_eq_bot_of_le_normalizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs

namespace Submission

/-- Strong embedding is invariant under conjugation. -/
theorem isStronglyEmbedded_map_mulAut_conj {G : Type*} [Group G] [Finite G] (M : Subgroup G) (g : G)
    (h : IsStronglyEmbedded M) :
    IsStronglyEmbedded (M.map (MulAut.conj g).toMonoidHom) := by
  have hker : ((MulAut.conj g).toMonoidHom).ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff (MulAut.conj g).toMonoidHom).mpr (MulAut.conj g).injective
  exact Commons.GroupTheory.StronglyEmbedded.stronglyEmbedded_map_of_surjective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).surjective M h.1 h.2.1 h.2.2
    (by rw [hker]; exact bot_le) (by rw [hker]; exact bot_le)
    (by rw [hker, Subgroup.card_bot]; exact odd_one)

/-- **The data of a split rank-one `(B,N)`-pair of characteristic two.**  `B` is the Borel
subgroup (strongly embedded), `U = O₂(B)` the unipotent radical (a Sylow `2`-subgroup), `T` an
odd-order complement of `U` in `B`, and `w` a Weyl element. -/
structure BenderPair (G : Type*) [Group G] [Finite G] where
  /-- the Borel subgroup. -/
  B : Subgroup G
  /-- the unipotent radical `O₂(B)`. -/
  U : Subgroup G
  /-- a complement of `U` in `B` (the "torus"). -/
  T : Subgroup G
  /-- the Weyl element. -/
  w : G
  /-- `B` is strongly embedded. -/
  hSemb : IsStronglyEmbedded B
  /-- `U` is a `2`-group. -/
  hU2 : IsPGroup 2 U
  /-- `U` is non-trivial. -/
  hUne : U ≠ ⊥
  /-- `|T|` is odd. -/
  hoddT : Odd (Nat.card T)
  /-- `B = U ⊔ T`. -/
  hB : B = U ⊔ T
  /-- `U ⊓ T = ⊥`. -/
  hUT : U ⊓ T = ⊥
  /-- `T` normalizes `U`. -/
  hTnU : T ≤ Subgroup.normalizer (U : Set G)
  /-- `w ∉ B`. -/
  hwB : w ∉ B
  /-- `w` normalizes `T`. -/
  hwT : w ∈ Subgroup.normalizer (T : Set G)
  /-- `T` acts fixed-point-freely on `U`: `C_U(T) = 1`. -/
  hCU : ∀ u ∈ U, (∀ t ∈ T, u * t = t * u) → u = 1
  /-- the Suzuki condition `[G : B] = |U| + 1`. -/
  hindex : B.index = Nat.card U + 1

namespace BenderPair

variable {G : Type*} [Group G] [Finite G]

theorem B_ne_top (P : BenderPair G) : P.B ≠ ⊤ := P.hSemb.1

theorem U_le_B (P : BenderPair G) : P.U ≤ P.B := by
  rw [P.hB]; exact le_sup_left

theorem T_le_B (P : BenderPair G) : P.T ≤ P.B := by
  rw [P.hB]; exact le_sup_right

/-- The Bender action of `G` on the cosets of the Borel subgroup. -/
theorem benderAction (P : BenderPair G) :
    MulAction.IsPretransitive G (G ⧸ P.B) ∧ 1 < Nat.card (G ⧸ P.B) ∧
      Even (Nat.card G) ∧
      ∀ t : G, orderOf t = 2 → ∃! x : G ⧸ P.B, t • x = x :=
  Commons.GroupTheory.Bender.isBenderAction_coset P.B P.B_ne_top P.hSemb.2.1 P.hSemb.2.2

/-- A non-trivial element of `U` fixes only the base point of the Bender action; equivalently `U`
acts regularly on the remaining `|U|` points. -/
theorem u_free (P : BenderPair G) (u : ↥P.U) (hu : u ≠ 1) {x : G ⧸ P.B}
    (hx : (u : G) • x = x) : x = ((1 : G) : G ⧸ P.B) := by
  obtain ⟨-, -, heven, hinv⟩ := P.benderAction
  have hfix : ∀ g : ↥P.U, (g : G) • ((1 : G) : G ⧸ P.B) = ((1 : G) : G ⧸ P.B) := by
    intro g
    change (g : G) ∈ MulAction.stabilizer G ((1 : G) : G ⧸ P.B)
    rw [MulAction.stabilizer_quotient P.B]
    exact P.U_le_B g.2
  refine Commons.GroupTheory.Bender.eq_of_smul_eq_self_of_mem_of_isPGroup_two (G := G)
    heven hinv P.hU2 hfix u.2 ?_ hx
  intro h
  exact hu (Subtype.ext h)

/-- `G` acts `2`-transitively on `G ⧸ B`. -/
theorem isMultiplyPretransitive_two (P : BenderPair G) :
    MulAction.IsMultiplyPretransitive G (G ⧸ P.B) 2 := by
  obtain ⟨htrans, hne, -, -⟩ := P.benderAction
  have hU : P.U ≤ MulAction.stabilizer G ((1 : G) : G ⧸ P.B) := by
    intro u hu
    rw [MulAction.stabilizer_quotient P.B]
    exact P.U_le_B hu
  have hreg : ∀ u : ↥P.U, u ≠ 1 →
      ∀ x : G ⧸ P.B, (u : G) • x = x → x = ((1 : G) : G ⧸ P.B) :=
    fun u hu x hx => P.u_free u hu hx
  have hcard : Nat.card (G ⧸ P.B) = Nat.card ↥P.U + 1 := by
    rw [← Subgroup.index_eq_card]; exact P.hindex
  exact Commons.GroupTheory.GroupAction.isMultiplyPretransitive_two_of_regular_of_card
    htrans hne ((1 : G) : G ⧸ P.B) (U := P.U) hU hreg hcard

/-- **The Bruhat decomposition** `G = B ∪ B w B` (the commons rank-one Bruhat lemma). -/
theorem bruhat (P : BenderPair G) :
    ∀ g : G, g ∈ P.B ∨ ∃ b₁ b₂ : ↥P.B, g = (b₁ : G) * P.w * (b₂ : G) := by
  haveI := P.isMultiplyPretransitive_two
  exact Commons.GroupTheory.BNPair.bruhat P.B P.w P.hwB

/-- `|U|` is even: `U` is a non-trivial `2`-group. -/
theorem even_card_U (P : BenderPair G) : Even (Nat.card ↥P.U) :=
  Commons.GroupTheory.BNPair.even_card_of_isPGroup_two P.U P.hU2 P.hUne

/-- The degree `[G : B] = |U| + 1` of the Bender action is odd. -/
theorem odd_index (P : BenderPair G) : Odd P.B.index := by
  rw [P.hindex]
  exact P.even_card_U.add_one

/-- **`N_G(T) = T ⋊ ⟨w⟩`**: the Weyl group of the rank-one pair has order dividing two. -/
theorem normalizer_T (P : BenderPair G) :
    Subgroup.normalizer (P.T : Set G) = P.T ⊔ Subgroup.zpowers P.w :=
  Commons.GroupTheory.BNPair.normalizer_eq_sup_zpowers P.B P.U P.T P.w P.hB P.hUT P.hTnU
    P.hwB P.hwT P.hCU P.hindex (fun u hu x hx => P.u_free u hu hx)

/-- The `T`-fixed points of the Bender action are exactly the base point and `w · base`. -/
theorem fixedPoints_eq_base_or_weyl (P : BenderPair G) {x : G ⧸ P.B}
    (hx : ∀ t ∈ P.T, t • x = x) :
    x = ((1 : G) : G ⧸ P.B) ∨ x = P.w • ((1 : G) : G ⧸ P.B) :=
  Commons.GroupTheory.BNPair.fixedPoints_eq_base_or_weyl P.B P.U P.T P.w P.hB P.hUT P.hTnU
    P.hwB P.hwT P.hCU P.hindex (fun u hu x hx => P.u_free u hu hx) hx

/-- `U` is a Sylow `2`-subgroup of `G` (the commons rank-one BN-pair lemma). -/
theorem not_two_dvd_index_U (P : BenderPair G) : ¬ 2 ∣ P.U.index :=
  Commons.GroupTheory.BNPair.unipotent_is_sylow P.B P.U P.T P.hB P.hUT P.hTnU P.hUne P.hU2
    P.hoddT P.hindex

/-- `U` really is a Sylow `2`-subgroup of `G`. -/
theorem exists_sylow_eq_U (P : BenderPair G) : ∃ S : Sylow 2 G, (S : Subgroup G) = P.U := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨P.hU2.toSylow P.not_two_dvd_index_U, IsPGroup.toSylow_coe _ _⟩

/-- `|G| = [G : B] · |B|`. -/
theorem card_eq_index_mul_card (P : BenderPair G) :
    Nat.card G = P.B.index * Nat.card ↥P.B :=
  (Subgroup.card_mul_index P.B).symm.trans (Nat.mul_comm _ _)

/-- **`N_G(U) = B`**: the Borel subgroup is the normalizer of its Sylow `2`-subgroup (the commons
rank-one BN-pair lemma `normalizer_eq_borel`). -/
theorem normalizer_U (P : BenderPair G) :
    Subgroup.normalizer (P.U : Set G) = P.B :=
  Commons.GroupTheory.BNPair.normalizer_eq_borel P.B P.U P.T P.hSemb.1 P.hSemb.2.1 P.hSemb.2.2
    P.hB P.hTnU P.hUne P.hU2

/-- The number of Sylow `2`-subgroups is the degree `[G : B]` of the Bender action. -/
theorem card_sylow_two (P : BenderPair G) : Nat.card (Sylow 2 G) = P.B.index := by
  obtain ⟨htrans, hne, heven, hinv⟩ := P.benderAction
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : P.U ≤ MulAction.stabilizer G ((1 : G) : G ⧸ P.B) := by
    intro u hu
    rw [MulAction.stabilizer_quotient P.B]
    exact P.U_le_B hu
  have hBn : MulAction.stabilizer G ((1 : G) : G ⧸ P.B) ≤
      Subgroup.normalizer (P.U : Set G) := by
    rw [P.normalizer_U]
    intro g hg
    rw [MulAction.stabilizer_quotient P.B] at hg
    exact hg
  have hmain :=
    Commons.GroupTheory.Bender.card_sylow_two_eq_index_stabilizer_of_isPGroup_of_odd_index
      (G := G) htrans hne heven hinv (((1 : G) : G ⧸ P.B))
      (U := P.U) P.hU2 P.not_two_dvd_index_U hU hBn
  rw [MulAction.stabilizer_quotient P.B] at hmain
  exact hmain

/-- **The order of a Bender group**: `|G| = |U| · |T| · (|U| + 1)`.  For the three families this
is `q(q-1)(q+1)`, `q²(q-1)(q²+1)` and `q³·|T|·(q³+1)`. -/
theorem card_eq_card_U_mul_card_T_mul_succ (P : BenderPair G) :
    Nat.card G = Nat.card ↥P.U * Nat.card ↥P.T * (Nat.card ↥P.U + 1) := by
  have hcardB : Nat.card ↥P.B = Nat.card ↥P.U * Nat.card ↥P.T := by
    rw [P.hB]
    exact Commons.GroupTheory.Subgroup.card_sup_of_inf_eq_bot_of_le_normalizer
      P.U P.T P.hTnU P.hUT
  rw [P.card_eq_index_mul_card, P.hindex, hcardB]
  ring

/-- The involution count: `#involutions(G) = [G : B] · #involutions(B)`. -/
theorem card_involutions (P : BenderPair G) :
    Nat.card {t : G // orderOf t = 2} =
      P.B.index * Nat.card {t : ↥P.B // orderOf t = 2} :=
  Commons.GroupTheory.StronglyEmbedded.card_involutions_eq_index_mul
    P.B P.B_ne_top P.hSemb.2.1 P.hSemb.2.2

/-- **Conjugation invariance of Bender groups**: a conjugate of the data of a rank-one
`(B,N)`-pair is again a rank-one `(B,N)`-pair.  (Bender's structure theorem is usually stated up
to conjugacy; this is the invariance that makes that formulation equivalent to `BenderPair`.) -/
noncomputable def conj (P : BenderPair G) (g : G) : BenderPair G where
  B := P.B.map (MulAut.conj g).toMonoidHom
  U := P.U.map (MulAut.conj g).toMonoidHom
  T := P.T.map (MulAut.conj g).toMonoidHom
  w := g * P.w * g⁻¹
  hSemb := isStronglyEmbedded_map_mulAut_conj P.B g P.hSemb
  hU2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := P.hU2.exists_card_eq
    refine IsPGroup.of_card (n := k) ?_
    rw [Subgroup.card_map_of_injective (MulEquiv.injective _), hk]
  hUne := by
    have hker : ((MulAut.conj g).toMonoidHom).ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff (MulAut.conj g).toMonoidHom).mpr (MulAut.conj g).injective
    intro h
    rw [Subgroup.map_eq_bot_iff, hker, le_bot_iff] at h
    exact P.hUne h
  hoddT := by
    rw [Subgroup.card_map_of_injective (MulEquiv.injective _)]
    exact P.hoddT
  hB := by rw [P.hB, Subgroup.map_sup]
  hUT := by
    have hker : ((MulAut.conj g).toMonoidHom).ker ≤ P.U := by
      rw [(MonoidHom.ker_eq_bot_iff (MulAut.conj g).toMonoidHom).mpr (MulAut.conj g).injective]
      exact bot_le
    rw [← Commons.GroupTheory.Subgroup.map_inf_eq_of_ker_le
        (MulAut.conj g).toMonoidHom P.U P.T hker, P.hUT, Subgroup.map_bot]
  hTnU := by
    rw [Commons.GroupTheory.Subgroup.normalizer_map_mulAut_conj]
    exact Subgroup.map_mono P.hTnU
  hwB := by
    intro h
    rw [Commons.GroupTheory.Subgroup.mem_map_mulAut_conj_iff] at h
    exact P.hwB (by simpa [mul_assoc] using h)
  hwT := by
    rw [Commons.GroupTheory.Subgroup.normalizer_map_mulAut_conj]
    exact Subgroup.mem_map.mpr ⟨P.w, P.hwT, rfl⟩
  hCU := by
    intro u hu hcent
    have hu' : g⁻¹ * u * g ∈ P.U :=
      (Commons.GroupTheory.Subgroup.mem_map_mulAut_conj_iff P.U g u).mp hu
    have hcent' : ∀ t ∈ P.T, (g⁻¹ * u * g) * t = t * (g⁻¹ * u * g) := by
      intro t ht
      have ht' : g * t * g⁻¹ ∈ P.T.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
      have h := hcent (g * t * g⁻¹) ht'
      calc (g⁻¹ * u * g) * t = g⁻¹ * (u * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * u) * g := by rw [h]
        _ = t * (g⁻¹ * u * g) := by group
    have h1 : g⁻¹ * u * g = 1 := P.hCU _ hu' hcent'
    calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  hindex := by
    have hker : ((MulAut.conj g).toMonoidHom).ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff (MulAut.conj g).toMonoidHom).mpr (MulAut.conj g).injective
    rw [Subgroup.index_map, hker, sup_bot_eq,
      MonoidHom.range_eq_top.mpr (MulAut.conj g).surjective, Subgroup.index_top, mul_one,
      Subgroup.card_map_of_injective (MulEquiv.injective _)]
    exact P.hindex

end BenderPair

end Submission
