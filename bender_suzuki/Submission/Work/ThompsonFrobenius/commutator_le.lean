import Mathlib
import Submission.Work.ThompsonFrobenius.GTDefs
import Submission.Work.ThompsonFrobenius.eq_of_le
import Submission.Work.ThompsonFrobenius.centralizer_pCore_le
import Submission.Work.ThompsonFrobenius.npc_quotient
import Submission.Work.ThompsonFrobenius.pCore_lt
import Submission.Work.ThompsonFrobenius.pCore_ne_bot
import Submission.Work.HallHigman.Basic
import Submission.Work.Frobenius.Complement.exists_invariant_sylow_of_isPGroup
import Submission.Work.NPC.All
import Submission.Work.PGroup.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# GT-6: `⁅K, K⁆ ≤ O_p(G)` (area `ThompsonFrobenius`)

Step GT-6 of `NOTES_LEAD_bs_thompson.md` (Farris §3.4 Step Four, second half).

Let `G` be the minimal counterexample with Sylow `p`-subgroup `P`, `H = O_p(G)`, and let `K` be the
preimage of the normal `p`-complement `K/H` of `G/H` (GT-3).  Then `K/H` is abelian, i.e.
`⁅K, K⁆ ≤ O_p(G)`.

The proof is Farris's counting argument.  Write `Ḡ = G/H`, and `P̄`, `K̄` for the images of `P` and
`K`.  Pick a prime `q ∣ |K̄|`; since `K̄ ⊴ Ḡ` and `P̄` is a `p`-group while `|K̄|` is prime to `p`,
the action of `P̄` on the Sylow `q`-subgroups of `K̄` has a fixed point `L̄`, and `V̄ := Z(L̄)` is a
nontrivial subgroup of `K̄` normalised by `P̄` (helpers `exists_invariant_sylow_of_normal`,
`le_normalizer_map_center`, `map_center_ne_bot_of_isPGroup`).  Pulling `V := V̄.comap (G → Ḡ)` back,
`P ≤ N_G(V)` while `V ⊄ P`, so `P < P ⊔ V`; GT-5 (`eq_of_le`) gives `P ⊔ V = G`, i.e.
`P̄ ⊔ V̄ = ⊤`.  Hence, by the counting lemma `card_le_card_of_isComplement_normalizes` applied to
`K̄.IsComplement' P̄`, `|K̄| = [Ḡ:P̄] ≤ |V̄| ≤ |L̄| ≤ |K̄|`; so `V̄ = K̄ = L̄` and `K̄ = Z(L̄) = Z(K̄)` is
abelian.  Finally `⁅K, K⁆ ≤ H` is the standard bridge from commutativity of the quotient
(`commutator_le_of_quotient_mul_comm`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Pointwise commutatorElement

namespace Work.ThompsonFrobenius

/-- The centre of a nontrivial finite `p`-group, viewed inside the ambient group, is nontrivial. -/
theorem map_center_ne_bot_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {L : Subgroup G} (hL : IsPGroup p L) (hne : L ≠ ⊥) :
    (((Subgroup.center ↥L).map L.subtype) : Subgroup G) ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hnt : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr hne
  haveI hcenter : Nontrivial ↥(Subgroup.center ↥L) := IsPGroup.center_nontrivial hL
  intro hbot
  have h1 : Subgroup.center ↥L ≤ L.subtype.ker :=
    (Subgroup.map_eq_bot_iff (Subgroup.center ↥L)).mp hbot
  rw [Subgroup.ker_subtype] at h1
  exact (Subgroup.nontrivial_iff_ne_bot (Subgroup.center ↥L)).mp hcenter (le_bot_iff.mp h1)

/-- If a subgroup `A` normalises `L`, it normalises the centre of `L` (viewed in the ambient
group): the centre is characteristic, hence invariant under the conjugation action of `A`. -/
theorem le_normalizer_map_center {G : Type*} [Group G] {A L : Subgroup G}
    (h : A ≤ Subgroup.normalizer (L : Set G)) :
    A ≤ Subgroup.normalizer (((Subgroup.center ↥L).map L.subtype) : Set G) := by
  have hmem : ∀ a ∈ A, ∀ k ∈ L, a * k * a⁻¹ ∈ L := Subgroup.le_normalizer_iff.mp h
  rw [Subgroup.le_normalizer_iff]
  intro a ha w hw
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hw
  have hazL : a * (z : G) * a⁻¹ ∈ L := hmem a ha (z : G) z.2
  refine Subgroup.mem_map.mpr ⟨⟨a * (z : G) * a⁻¹, hazL⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have ha' : a⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ (h ha)
  have hy : a⁻¹ * (y : G) * a ∈ L := by
    simpa using (Subgroup.le_normalizer_iff.mp le_rfl) a⁻¹ ha' (y : G) y.2
  have hcomm : (a⁻¹ * (y : G) * a) * (z : G) = (z : G) * (a⁻¹ * (y : G) * a) := by
    simpa using congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hz (⟨a⁻¹ * (y : G) * a, hy⟩ : ↥L))
  calc (y : G) * (a * (z : G) * a⁻¹)
      = a * ((a⁻¹ * (y : G) * a) * (z : G)) * a⁻¹ := by group
    _ = a * ((z : G) * (a⁻¹ * (y : G) * a)) * a⁻¹ := by rw [hcomm]
    _ = (a * (z : G) * a⁻¹) * (y : G) := by group

/-- If the image of `K` in `G ⧸ H` is abelian, then `⁅K, K⁆ ≤ H`. -/
theorem commutator_le_of_quotient_mul_comm {G : Type*} [Group G] {H K : Subgroup G} [H.Normal]
    (hab : ∀ x y : ↥(K.map (QuotientGroup.mk' H)), x * y = y * x) :
    ⁅K, K⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hx : (QuotientGroup.mk' H) a ∈ K.map (QuotientGroup.mk' H) :=
    Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  have hy : (QuotientGroup.mk' H) b ∈ K.map (QuotientGroup.mk' H) :=
    Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
  have hcomm : (QuotientGroup.mk' H) a * (QuotientGroup.mk' H) b =
      (QuotientGroup.mk' H) b * (QuotientGroup.mk' H) a :=
    congrArg Subtype.val (hab ⟨_, hx⟩ ⟨_, hy⟩)
  have h2 : (QuotientGroup.mk' H) ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact hcomm
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h2
  exact h2

/-- Counting lemma for GT-6.  Let `N` be a complement of `S` in a finite group `X` (so that
`|N| = [X : S]`), and let `V` be a subgroup normalised by `S` with `S ⊔ V = X`.  Then `|N| ≤ |V|`;
indeed `V * S = X`, so `|N| * |S| = |X| ≤ |V| * |S|`, and we cancel `|S|`. -/
theorem card_le_card_of_isComplement_sup_eq_top {X : Type*} [Group X] [Finite X]
    {N S V : Subgroup X} (hcomp : N.IsComplement' S) (hsup : S ⊔ V = ⊤)
    (hSV : S ≤ Subgroup.normalizer (V : Set X)) :
    Nat.card ↥N ≤ Nat.card ↥V := by
  have hmul : (V : Set X) * (S : Set X) = Set.univ := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left V S hSV, sup_comm, hsup]
    rfl
  have hsurj : Function.Surjective (fun p : ↥V × ↥S => ((p.1 : X) * (p.2 : X))) := by
    intro x
    have hx : x ∈ (V : Set X) * (S : Set X) := by rw [hmul]; exact Set.mem_univ x
    obtain ⟨v, hv, s, hs, hvs⟩ := hx
    exact ⟨(⟨v, hv⟩, ⟨s, hs⟩), hvs⟩
  have hcard : Nat.card X ≤ Nat.card ↥V * Nat.card ↥S := by
    calc Nat.card X ≤ Nat.card (↥V × ↥S) := Nat.card_le_card_of_surjective _ hsurj
      _ = Nat.card ↥V * Nat.card ↥S := Nat.card_prod _ _
  have h2 : Nat.card ↥N * Nat.card ↥S = Nat.card X := hcomp.card_mul_card
  have hpos : 0 < Nat.card ↥S := Nat.card_pos
  exact Nat.le_of_mul_le_mul_right (by rw [h2]; exact hcard) hpos

/-- **Invariant Sylow `q`-subgroup.**  Let `A` be a `p`-subgroup of a finite group `X` and let
`N ⊴ X` have order prime to `p`.  Then there is a Sylow `q`-subgroup `L` of `N`, normalised by
`A`.  (Frattini/orbit-counting: `A` acts on the set of Sylow `q`-subgroups of `N`, whose
cardinality divides `|N|` and is therefore prime to `p`.) -/
theorem exists_invariant_sylow_of_normal {X : Type*} [Group X] [Finite X] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) {A N : Subgroup X} (hA : IsPGroup p A) (hN : N.Normal)
    (hcop : (Nat.card ↥N).Coprime p) :
    ∃ L : Subgroup X, L ≤ N ∧ IsPGroup q L ∧ Nat.card ↥L = q ^ (Nat.card ↥N).factorization q ∧
      A ≤ Subgroup.normalizer (L : Set X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  -- the conjugation action of `A` on the normal subgroup `N`
  let smulFn : ↥A → ↥N → ↥N :=
    fun a x => ⟨(a : X) * (x : X) * (a : X)⁻¹, hN.conj_mem (x : X) x.2 (a : X)⟩
  letI : MulDistribMulAction ↥A ↥N :=
    { smul := smulFn
      one_smul := fun x => Subtype.ext (by show (smulFn 1 x : X) = (x : X); simp [smulFn])
      mul_smul := fun a b x => Subtype.ext (by
        show (smulFn (a * b) x : X) = (smulFn a (smulFn b x) : X)
        simp only [smulFn]
        rw [Subgroup.coe_mul A a b]
        group)
      smul_one := fun a => Subtype.ext (by show (smulFn a 1 : X) = (1 : X); simp [smulFn])
      smul_mul := fun a y z => Subtype.ext (by
        show (smulFn a (y * z) : X) = ((smulFn a y) * (smulFn a z) : X)
        simp only [smulFn]
        rw [Subgroup.coe_mul N y z]
        group) }
  have hcop2 : (Nat.card ↥A).Coprime (Nat.card ↥N) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA
    rw [hn]
    exact hcop.symm.pow_left n
  obtain ⟨S, hS⟩ :=
    Work.Frobenius.Complement.exists_invariant_sylow_of_isPGroup hp hA hcop2 hq
  refine ⟨(S : Subgroup ↥N).map N.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · exact IsPGroup.map S.isPGroup' N.subtype
  · rw [Subgroup.card_map_of_injective N.subtype_injective, Sylow.card_eq_multiplicity]
  · rw [Subgroup.le_normalizer_iff]
    intro a ha l hl
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hl
    have hx' : (⟨a, ha⟩ : ↥A) • x ∈ (S : Subgroup ↥N) := (hS ⟨a, ha⟩ x).mp hx
    refine Subgroup.mem_map.mpr ⟨(⟨a, ha⟩ : ↥A) • x, hx', ?_⟩
    show (smulFn ⟨a, ha⟩ x : X) = a * (x : X) * a⁻¹
    rfl

theorem commutator_le {p : ℕ} {G : Type} [Group G] [Finite G] {P : Sylow p G}
    (h : Work.ThompsonFrobenius.GTMinimal p G P) {K : Subgroup G}
    (hK : Work.NPC.IsNormalPComplement p (K.map (QuotientGroup.mk' (Work.HallHigman.pCore p G))))
    (hHK : Work.HallHigman.pCore p G ≤ K) : ⁅K, K⁆ ≤ Work.HallHigman.pCore p G := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  let H : Subgroup G := Work.HallHigman.pCore p G
  haveI hHnormal : H.Normal := inferInstance
  let π : G →* G ⧸ H := QuotientGroup.mk' H
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective H
  have hker : π.ker = H := QuotientGroup.ker_mk' H
  haveI hfinQ : Finite (G ⧸ H) := ((finite_iff_subgroup_quotient H).mp inferInstance).2
  let Kbar : Subgroup (G ⧸ H) := K.map π
  have hKbar_normal : Kbar.Normal := hK.normal
  have hKbar_cop : (Nat.card ↥Kbar).Coprime p := hK.coprime_card
  by_cases hKbot : Kbar = ⊥
  · -- `K = H`: then `K` is a `p`-group and the claim is immediate.
    have hKH : K ≤ H := by
      intro x hx
      have hxK : π x ∈ Kbar := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rw [hKbot] at hxK
      have hx1 : π x = 1 := by simpa using hxK
      rw [← hker]
      exact MonoidHom.mem_ker.mpr hx1
    have hKeq : K = H := le_antisymm hKH hHK
    rw [hKeq]
    exact Subgroup.commutator_le_left H H
  · -- `K̄ ≠ 1`: pick a prime `q ∣ |K̄|` and an invariant Sylow `q`-subgroup of `K̄`.
    have hKbar_ne1 : Nat.card ↥Kbar ≠ 1 := fun h1 => hKbot (Subgroup.card_eq_one.mp h1)
    obtain ⟨q, hqprime, hqdiv⟩ := Nat.exists_prime_and_dvd hKbar_ne1
    let Pbar : Sylow p (G ⧸ H) := P.mapSurjective hπsurj
    have hPbar_coe : (Pbar : Subgroup (G ⧸ H)) = (P : Subgroup G).map π := rfl
    have hPbar_pg : IsPGroup p ↥(Pbar : Subgroup (G ⧸ H)) := Pbar.isPGroup'
    obtain ⟨L, hLle, hLpg, hLcard, hLinv⟩ :=
      exists_invariant_sylow_of_normal (A := (Pbar : Subgroup (G ⧸ H))) (N := Kbar)
        h.prime hqprime hPbar_pg hKbar_normal hKbar_cop
    have hLne : L ≠ ⊥ := by
      intro hbot
      have hone : Nat.card ↥L = 1 := Subgroup.card_eq_one.mpr hbot
      rw [hLcard] at hone
      have hk0 : (Nat.card ↥Kbar).factorization q ≠ 0 := by
        have h2 : 1 ≤ (Nat.card ↥Kbar).factorization q :=
          (hqprime.dvd_iff_one_le_factorization (Nat.card_pos.ne')).mp hqdiv
        omega
      have h3 : 1 < q ^ (Nat.card ↥Kbar).factorization q := Nat.one_lt_pow hk0 hqprime.one_lt
      rw [hone] at h3
      exact lt_irrefl 1 h3
    -- the centre `V̄` of `L̄`, inside `Ḡ`
    let Vbar : Subgroup (G ⧸ H) := (Subgroup.center ↥L).map L.subtype
    have hVbar_le_L : Vbar ≤ L := Subgroup.map_subtype_le _
    have hVbar_le_Kbar : Vbar ≤ Kbar := hVbar_le_L.trans hLle
    have hVbar_ne : Vbar ≠ ⊥ := map_center_ne_bot_of_isPGroup hqprime hLpg hLne
    have hPbar_le_normV :
        (Pbar : Subgroup (G ⧸ H)) ≤ Subgroup.normalizer (Vbar : Set (G ⧸ H)) :=
      le_normalizer_map_center hLinv
    -- its preimage `V` in `G`
    let V : Subgroup G := Vbar.comap π
    have hVmap : V.map π = Vbar := by
      show (Vbar.comap π).map π = Vbar
      rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hπsurj, top_inf_eq]
    have hHleV : H ≤ V := by
      intro x hx
      show π x ∈ Vbar
      have hx1 : π x = 1 := by
        rw [← MonoidHom.mem_ker, hker]
        exact hx
      rw [hx1]
      exact Vbar.one_mem
    have hVleK : V ≤ K := by
      intro x hx
      have hx' : π x ∈ Kbar := hVbar_le_Kbar hx
      obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hx'
      have hmem : x * k⁻¹ ∈ H := by
        rw [← hker]
        show π (x * k⁻¹) = 1
        rw [map_mul, map_inv, hkx]
        simp
      have hxeq : x = (x * k⁻¹) * k := by group
      rw [hxeq]
      exact K.mul_mem (hHK hmem) hk
    have hPleNV : (P : Subgroup G) ≤ Subgroup.normalizer (V : Set G) := by
      have h1 : (P : Subgroup G) ≤
          Subgroup.comap π (Subgroup.normalizer (Vbar : Set (G ⧸ H))) :=
        (Subgroup.le_comap_map π P).trans (Subgroup.comap_mono hPbar_le_normV)
      exact h1.trans (Subgroup.le_normalizer_comap π)
    -- `V ⊄ P`, because `V̄ ≠ 1` while `V̄ ⊓ P̄ = 1`
    have hVnotleP : ¬ V ≤ (P : Subgroup G) := by
      intro hVP
      have hVbar_le_Pbar : Vbar ≤ (Pbar : Subgroup (G ⧸ H)) := by
        rw [← hVmap, hPbar_coe]
        exact Subgroup.map_mono hVP
      have hVp : IsPGroup p ↥Vbar := Pbar.isPGroup'.to_le hVbar_le_Pbar
      have hVcop : (Nat.card ↥Vbar).Coprime p :=
        Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hVbar_le_Kbar) hKbar_cop
      rcases hVp.card_eq_or_dvd with h1 | h1
      · exact hVbar_ne (Subgroup.card_eq_one.mp h1)
      · exact h.prime.not_dvd_one (by
          have h2 : p ∣ (Nat.card ↥Vbar).gcd p := Nat.dvd_gcd h1 (dvd_refl p)
          rwa [hVcop] at h2)
    -- GT-5: `P` is maximal, so `P ⊔ V = G`, hence `P̄ ⊔ V̄ = ⊤`
    have hsup : (P : Subgroup G) ⊔ V = ⊤ := by
      rcases eq_of_le h le_sup_left with h1 | h1
      · exact absurd (sup_eq_left.mp h1) hVnotleP
      · exact h1
    have hPbar_sup_Vbar : (Pbar : Subgroup (G ⧸ H)) ⊔ Vbar = ⊤ := by
      have h1 := congrArg (Subgroup.map π) hsup
      rw [Subgroup.map_sup, Subgroup.map_top_of_surjective π hπsurj, ← hPbar_coe, hVmap] at h1
      exact h1
    -- counting
    have hcard_le : Nat.card ↥Kbar ≤ Nat.card ↥Vbar :=
      card_le_card_of_isComplement_sup_eq_top
        (Work.NPC.Basic.isNormalPComplement_complement_sylow hK Pbar) hPbar_sup_Vbar
        hPbar_le_normV
    have hcardV_L : Nat.card ↥Vbar ≤ Nat.card ↥L :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hVbar_le_L)
    have hVbar_eq : Vbar = Kbar := Subgroup.eq_of_le_of_card_ge hVbar_le_Kbar hcard_le
    have hL_eq : L = Kbar := Subgroup.eq_of_le_of_card_ge hLle (hcard_le.trans hcardV_L)
    -- hence `K̄ = Z(K̄)` is abelian
    have hab : ∀ x y : ↥Kbar, x * y = y * x := by
      have hcenter_eq : (Subgroup.center ↥Kbar).map Kbar.subtype = Kbar := by
        have hh : (Subgroup.center ↥L).map L.subtype = Kbar := hVbar_eq
        rw [hL_eq] at hh
        exact hh
      intro x y
      have hcx : (x : G ⧸ H) ∈ (Subgroup.center ↥Kbar).map Kbar.subtype := by
        rw [hcenter_eq]
        exact x.2
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hcx
      have hzy : y * z = z * y := Subgroup.mem_center_iff.mp hz y
      have hzx' : z = x := Subtype.ext hzx
      rw [← hzx']
      exact hzy.symm
    exact commutator_le_of_quotient_mul_comm hab

end Work.ThompsonFrobenius
