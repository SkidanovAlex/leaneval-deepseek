import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.thm26_aux
import Submission.Work.CORE2A.lemma22
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.OutsideS0OrderTwo
import Submission.Work.CORE3.SylowLeCentralizer
import Submission.Work.CORE3.H_eq_U_sup_S
import Submission.Work.CORE3.isPGroup_le_or_inf_eq_bot_of_isHallIn

set_option linter.style.haveILetI false

namespace Work.CORE3

open Work.GW2
open Subgroup

/-! ## Support API for `Work.CORE3.Case1aSetup`

The five lemmas below are elementary group theory, stated in the vocabulary of
`Work.GW2`; they are the "characteristic subgroup" and "prime core" tools the main argument
uses. -/

/-- Conjugation by an element of `N_G(K)` as an automorphism of `↥K`. -/
def c1aConjMulAut {G : Type} [Group G] (K : Subgroup G) {h : G}
    (hh : h ∈ Subgroup.normalizer (K : Set G)) : MulAut ↥K where
  toFun x := ⟨h * (x : G) * h⁻¹, ((Subgroup.mem_normalizer_iff.mp hh) (x : G)).mp x.2⟩
  invFun x := ⟨h⁻¹ * (x : G) * h, by
    have hh' : h⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normalizer (K : Set G)).inv_mem hh
    simpa using ((Subgroup.mem_normalizer_iff.mp hh') (x : G)).mp x.2⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

theorem c1aConjMulAut_apply {G : Type} [Group G] (K : Subgroup G) {h : G}
    (hh : h ∈ Subgroup.normalizer (K : Set G)) (x : ↥K) :
    ((c1aConjMulAut K hh x : ↥K) : G) = h * (x : G) * h⁻¹ := rfl

/-- If `N` is characteristic in `↥K`, then `N_G(K)` normalizes the image of `N` in `G`. -/
theorem c1aConjSub_map_subtype_eq_self {G : Type} [Group G] {K : Subgroup G}
    {N : Subgroup ↥K} (hN : N.Characteristic) {h : G}
    (hh : h ∈ Subgroup.normalizer (K : Set G)) :
    conjSub h (N.map K.subtype) = N.map K.subtype := by
  have hfix : N.map (c1aConjMulAut K hh).toMonoidHom = N :=
    Subgroup.characteristic_iff_map_eq.mp hN (c1aConjMulAut K hh)
  have hcomp : (MulAut.conj h).toMonoidHom.comp K.subtype
      = K.subtype.comp (c1aConjMulAut K hh).toMonoidHom := by
    ext x
    simp [c1aConjMulAut_apply, MulAut.conj_apply]
  rw [conjSub, Subgroup.map_map, hcomp, ← Subgroup.map_map, hfix]

/-- `N_G(K) ≤ N_G(O_q(K))`: the `q`-core of `K` is characteristic in `↥K`, and conjugation by
an element of `N_G(K)` is an automorphism of `↥K`. -/
theorem c1aLe_normalizer_pCoreIn {G : Type} [Group G] [Finite G] (q : ℕ) [Fact q.Prime]
    (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (Work.GW2.pCoreIn q K : Set G) := by
  haveI hchar : (Work.GW2.pCore q ↥K).Characteristic := by
    rw [Work.CORE2A.pCore_eq_opCore (G := ↥K)]
    exact OddOrder.Isaacs.Ch01.opCore.characteristic q ↥K
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmain := c1aConjSub_map_subtype_eq_self (K := K) (N := Work.GW2.pCore q ↥K)
    hchar hh
  simpa [Work.GW2.pCoreIn, conjSub] using hmain

/-- `F(K)` is characteristic in `↥K`. -/
theorem c1aFitting_characteristic {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    (Work.GW2.fitting ↥K).Characteristic := by
  rw [Work.CORE2A.fitting_eq_isaacsFitting (G := ↥K)]
  haveI : ∀ p : Nat.Primes, (OddOrder.Isaacs.Ch01.opCore p.val ↥K).Characteristic :=
    fun p => OddOrder.Isaacs.Ch01.opCore.characteristic p.val ↥K
  infer_instance

/-- `N_G(K) ≤ N_G(F(K))`: the Fitting subgroup is characteristic in `↥K`. -/
theorem c1aConjSub_fittingIn_eq_self {G : Type} [Group G] [Finite G] {K : Subgroup G} {h : G}
    (hh : h ∈ Subgroup.normalizer (K : Set G)) :
    conjSub h (Work.GW2.fittingIn K) = Work.GW2.fittingIn K := by
  haveI hchar : (Work.GW2.fitting ↥K).Characteristic := c1aFitting_characteristic K
  have hmain := c1aConjSub_map_subtype_eq_self (K := K) (N := Work.GW2.fitting ↥K)
    hchar hh
  simpa [Work.GW2.fittingIn, conjSub] using hmain

/-- `F(K) ≤ K`. -/
theorem c1aFittingIn_le {G : Type} [Group G] (K : Subgroup G) :
    Work.GW2.fittingIn K ≤ K := Subgroup.map_subtype_le _

/-- `O_q(K) ≤ K`. -/
theorem c1aPcoreIn_le_self {G : Type} [Group G] (q : ℕ) (K : Subgroup G) :
    Work.GW2.pCoreIn q K ≤ K := Subgroup.map_subtype_le _

/-- `O_q(K) ≤ F(K)`. -/
theorem c1aPcoreIn_le_fittingIn {G : Type} [Group G] [Finite G] (q : ℕ) [Fact q.Prime]
    (K : Subgroup G) : Work.GW2.pCoreIn q K ≤ Work.GW2.fittingIn K := by
  rw [Work.GW2.pCoreIn, Work.GW2.fittingIn, Subgroup.map_subtype_le_map_subtype,
    Work.CORE2A.pCore_eq_opCore (G := ↥K), Work.CORE2A.fitting_eq_isaacsFitting (G := ↥K)]
  rw [show OddOrder.Isaacs.Ch01.fitting ↥K
      = ⨆ p : Nat.Primes, OddOrder.Isaacs.Ch01.opCore p.val ↥K from rfl]
  exact le_iSup (fun p : Nat.Primes => OddOrder.Isaacs.Ch01.opCore p.val ↥K)
    ⟨q, (inferInstance : Fact q.Prime).out⟩

/-- `O_q(K)` is a `q`-group. -/
theorem c1aIsPGroup_pCoreIn {G : Type} [Group G] [Finite G] (q : ℕ) [Fact q.Prime]
    (K : Subgroup G) : IsPGroup q (Work.GW2.pCoreIn q K) := by
  rw [Work.GW2.pCoreIn, Work.CORE2A.pCore_eq_opCore (G := ↥K)]
  exact (OddOrder.Isaacs.Ch01.opCore_isPGroup q ↥K).map K.subtype

/-- The image in `G` of a normal subgroup of `↥K` is normalized by `K`. -/
theorem c1aLe_normalizer_map_subtype {G : Type} [Group G] {K : Subgroup G}
    {N : Subgroup K} (hN : N.Normal) :
    K ≤ Subgroup.normalizer ((N.map K.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro k hk n hn
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn
  exact Subgroup.mem_map.mpr ⟨⟨k, hk⟩ * m * ⟨k, hk⟩⁻¹, hN.conj_mem m hm ⟨k, hk⟩, by simp⟩

/-- If `x * x = 1` then `z = y⁻¹ * (x * y * x⁻¹)` is inverted by `x`. -/
theorem c1aInverted_of_sq_eq_one {G : Type} [Group G] {x y : G} (hx : x * x = 1) :
    x * (y⁻¹ * (x * y * x⁻¹)) * x⁻¹ = (y⁻¹ * (x * y * x⁻¹))⁻¹ := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hx2inv : x⁻¹ * x⁻¹ = 1 := by rw [← mul_inv_rev, hx, inv_one]
  calc x * (y⁻¹ * (x * y * x⁻¹)) * x⁻¹
      = x * y⁻¹ * x * y * (x⁻¹ * x⁻¹) := by group
    _ = x * y⁻¹ * x * y * 1 := by rw [hx2inv]
    _ = x * y⁻¹ * x * y := by rw [mul_one]
    _ = x * y⁻¹ * x⁻¹ * y := by rw [hxinv]
    _ = (y⁻¹ * (x * y * x⁻¹))⁻¹ := by group

/-- An involution normalizing `Q` with no non-trivial inverted element of `Q` centralizes `Q`. -/
theorem c1aCentralizer_of_no_inverted {G : Type} [Group G] {Q : Subgroup G} {x : G}
    (hx : x * x = 1) (hnorm : x ∈ Subgroup.normalizer (Q : Set G))
    (h : ∀ y ∈ Q, x * y * x⁻¹ = y⁻¹ → y = 1) :
    Q ≤ Subgroup.centralizer ({x} : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  rw [hw]
  have hzQ : y⁻¹ * (x * y * x⁻¹) ∈ Q :=
    Q.mul_mem (Q.inv_mem hy) (((Subgroup.mem_normalizer_iff.mp hnorm) y).mp hy)
  have hzz : x * (y⁻¹ * (x * y * x⁻¹)) * x⁻¹ = (y⁻¹ * (x * y * x⁻¹))⁻¹ :=
    c1aInverted_of_sq_eq_one hx
  have hz1 : y⁻¹ * (x * y * x⁻¹) = 1 := h _ hzQ hzz
  have hxy : x * y * x⁻¹ = y := by
    calc x * y * x⁻¹ = y * (y⁻¹ * (x * y * x⁻¹)) := by group
      _ = y := by rw [hz1, mul_one]
  have hcomm : x * y = y * x := by
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [hxy]
  exact hcomm

/-- The Fitting subgroup is the join of the prime cores: `F(K) = ⨆ p, O_p(K)`. -/
theorem c1aFittingIn_eq_iSup_pCoreIn {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    Work.GW2.fittingIn K = ⨆ p : Nat.Primes, Work.GW2.pCoreIn p.val K := by
  rw [Work.GW2.fittingIn, Work.CORE2A.fitting_eq_isaacsFitting (G := ↥K)]
  rw [show OddOrder.Isaacs.Ch01.fitting ↥K
      = ⨆ p : Nat.Primes, OddOrder.Isaacs.Ch01.opCore p.val ↥K from rfl]
  rw [Subgroup.map_iSup]
  refine iSup_congr fun p => ?_
  haveI : Fact p.val.Prime := ⟨p.2⟩
  rw [Work.GW2.pCoreIn, Work.CORE2A.pCore_eq_opCore (G := ↥K)]

end Work.CORE3

namespace Work.CORE3

namespace Work.CORE3

open Work.GW2

/-- Bender 1981 §3, p. 222, first subcase (`O₂(Ĥ) ≤ S₀`, whence `Ĥ = H`).  Deliverable
`Work.GW2.Case1aSetupProp`, with the area's six inputs bundled in `I : Case1Inputs`.

From `Case1 B` (so `I_U(s)` is Hall in `F(U)` for `s ∈ S − S₀`, and `N_G(X) ≤ H` for
`1 ≠ X ≤ F(U)`) and `Ĥ = H`: if `S₀` centralized `U`, then `I_U(s)` would be a normal subgroup
of `U` (the action of `S = S₀ ∪ S₀s` on odd `U` factors through `s`, and an inverted set of an
involution is a normal subgroup, Bender 1.5(iii)), contradicting Lemma 2.2 (`I.h22`); hence
`[S₀,U] ≠ 1`.  Since `U = F(U)·C_U(S)` and some `p ∈ π(F(U))` has `[S₀,O_p(U)] ≠ 1`, there are
involutions `t₁,t₂ ∈ S − S₀` with `P = O_p(U)` centralized by `t₁` and inverted by `t₂`
(`t₁t₂` generates `S₀`). -/
theorem Case1aSetup (I : Case1Inputs) : Case1aSetupProp := by
  intro G instG finG hFT hBc B h1 hHhat
  classical
  -- ## Step 0: the dihedral Sylow 2-subgroup and its reflections
  obtain ⟨n, hn2, hdih⟩ := SylowDihedral G hBc B
  obtain ⟨s, hsS, hsS0⟩ := CORE2A.bSetup_exists_mem_S_not_mem_S0 B
  -- a generator `g` of the cyclic subgroup `S₀`
  obtain ⟨g, hzg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top B.S0).mp B.S0_cyclic
  have hgS0 : g ∈ B.S0 := hzg ▸ Subgroup.mem_zpowers g
  have hgS : g ∈ (B.S : Subgroup G) := B.S0_le hgS0
  have hS0zp : B.S0 = Subgroup.zpowers g := hzg.symm
  have hrefl : ∀ x ∈ (B.S : Subgroup G), x ∉ B.S0 → orderOf x = 2 :=
    fun x hx hx0 => OutsideS0OrderTwo G hBc B n hn2 hdih x hx hx0
  have hsord : orderOf s = 2 := hrefl s hsS hsS0
  have hss : s * s = 1 := by
    have h : s ^ 2 = 1 := by rw [← hsord]; exact pow_orderOf_eq_one s
    simpa [pow_two] using h
  -- the second reflection `s₂ = s·g`
  set s2 : G := s * g with hs2def
  have hs2S : s2 ∈ (B.S : Subgroup G) := by
    rw [hs2def]; exact (B.S : Subgroup G).mul_mem hsS hgS
  have hs2S0 : s2 ∉ B.S0 := by
    intro hmem
    rw [hs2def] at hmem
    refine hsS0 ?_
    have h1' : s = (s * g) * g⁻¹ := by group
    rw [h1']
    exact B.S0.mul_mem hmem (B.S0.inv_mem hgS0)
  have hs2ord : orderOf s2 = 2 := hrefl s2 hs2S hs2S0
  have hs2s2 : s2 * s2 = 1 := by
    have h : s2 ^ 2 = 1 := by rw [← hs2ord]; exact pow_orderOf_eq_one s2
    simpa [pow_two] using h
  -- `g = s·s₂`
  have hgs : g = s * s2 := by rw [hs2def, ← mul_assoc, hss, one_mul]
  -- ## Step 1: the package attached to a reflection `x ∈ S − S₀`
  have key : ∀ x : G, x ∈ (B.S : Subgroup G) → x ∉ B.S0 → orderOf x = 2 →
      ∃ Ix : Subgroup G,
        (Ix : Set G) = invSet B.U x ∧
        (Ix.subgroupOf B.U).Normal ∧
        Ix ≤ fittingIn B.U ∧
        (∀ q : ℕ, q.Prime → pCoreIn q B.U ≤ Ix ∨ pCoreIn q B.U ⊓ Ix = ⊥) ∧
        (∀ q : ℕ, q.Prime → pCoreIn q B.U ⊓ Ix = ⊥ →
            pCoreIn q B.U ≤ Subgroup.centralizer ({x} : Set G)) ∧
        (∀ q : ℕ, q.Prime → pCoreIn q B.U ≤ Ix → Inverts x (pCoreIn q B.U)) := by
    intro x hxS hxS0 hxord
    -- Case (1) of Theorem 2.10 gives `I_U(x)`
    obtain ⟨Ix, hIxc, hHallx⟩ := h1.1 x hxS hxS0
    have hx2 : x * x = 1 := by
      have h : x ^ 2 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
      simpa [pow_two] using h
    -- `x` normalizes `U`
    have hxU : x ∈ Subgroup.normalizer (B.U : Set G) := CORE2A.bender_s_mem_normalizer_U B hxS
    -- Bender 1.5 for `s = x` and `X = U`
    obtain ⟨h15a, h15b, h15c⟩ := I.T.c15 G I.T.ft B.U x hxord (CORE2A.bSetup_U_odd B) hxU
    have hInorm : (Ix.subgroupOf B.U).Normal := (h15c Ix hIxc).2.1
    have hIleF : Ix ≤ fittingIn B.U := (h15c Ix hIxc).2.2
    have hIleU : Ix ≤ B.U := le_trans hIleF (c1aFittingIn_le B.U)
    -- `I_U(x)` is normal in `F(U)`, so the Hall/prime-core dichotomy applies
    have hInorm' : B.U ≤ Subgroup.normalizer (Ix : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hIleU).mp hInorm
    have hInormF : (Ix.subgroupOf (fittingIn B.U)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hIleF).mpr
        (le_trans (c1aFittingIn_le B.U) hInorm')
    refine ⟨Ix, hIxc, hInorm, hIleF, ?_, ?_, ?_⟩
    · -- dichotomy: `O_q(U) ⊆ I_U(x)` or `O_q(U) ⊓ I_U(x) = ⊥`
      intro q hq
      haveI : Fact q.Prime := ⟨hq⟩
      exact isPGroup_le_or_inf_eq_bot_of_isHallIn hq hHallx hInormF
        (c1aPcoreIn_le_fittingIn q B.U) (c1aIsPGroup_pCoreIn q B.U)
    · -- a prime core disjoint from `I_U(x)` is centralized by `x`
      intro q hq hdisj
      haveI : Fact q.Prime := ⟨hq⟩
      have hxN : x ∈ Subgroup.normalizer (pCoreIn q B.U : Set G) :=
        c1aLe_normalizer_pCoreIn q B.U hxU
      refine c1aCentralizer_of_no_inverted hx2 hxN ?_
      intro y hy hyinv
      have hyI : y ∈ Ix := by
        have hmem : y ∈ invSet B.U x :=
          CORE2A.mem_invSet.mpr ⟨c1aPcoreIn_le_self q B.U hy, hyinv⟩
        show y ∈ (Ix : Set G)
        rw [hIxc]
        exact hmem
      have hybot : y ∈ pCoreIn q B.U ⊓ Ix := ⟨hy, hyI⟩
      rw [hdisj] at hybot
      simpa using hybot
    · -- a prime core inside `I_U(x)` is inverted by `x`
      intro q hq hle y hy
      have hmem : y ∈ (Ix : Set G) := hle hy
      rw [hIxc] at hmem
      exact (CORE2A.mem_invSet.mp hmem).2
  obtain ⟨Is, hIsc, hIsnorm, hIsleF, hIsdich, hIscent, hIsinv⟩ := key s hsS hsS0 hsord
  obtain ⟨Is2, hIs2c, hIs2norm, hIs2leF, hIs2dich, hIs2cent, hIs2inv⟩ :=
    key s2 hs2S hs2S0 hs2ord
  -- ## Step 2: the case distinction on the behaviour of the two reflections
  by_cases hcase : ∃ q : ℕ, q.Prime ∧
      ((pCoreIn q B.U ≤ Is ∧ ¬ pCoreIn q B.U ≤ Is2) ∨
       (pCoreIn q B.U ≤ Is2 ∧ ¬ pCoreIn q B.U ≤ Is))
  · -- ### Case A: some prime is treated differently by `s` and `s₂`
    obtain ⟨q, hq, hqr⟩ := hcase
    haveI : Fact q.Prime := ⟨hq⟩
    have hOqne : pCoreIn q B.U ≠ ⊥ := by
      intro hbot
      rcases hqr with ⟨-, h2'⟩ | ⟨-, h2'⟩
      · exact h2' (by rw [hbot]; exact bot_le)
      · exact h2' (by rw [hbot]; exact bot_le)
    have hdvdO : q ∣ Nat.card (pCoreIn q B.U) := by
      obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (c1aIsPGroup_pCoreIn q B.U)
      have hcard : Nat.card (pCoreIn q B.U) ≠ 1 := by
        intro hc
        exact hOqne (Subgroup.card_eq_one.mp hc)
      have ha0 : a ≠ 0 := by
        intro h0
        exact hcard (by rw [ha, h0, pow_zero])
      obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha0
      exact ⟨q ^ b, by rw [ha, pow_succ']⟩
    have hpmem : q ∈ primesOf (fittingIn B.U) := by
      show q ∈ (Nat.card (fittingIn B.U)).primeFactors
      rw [Nat.mem_primeFactors]
      exact ⟨hq, dvd_trans hdvdO (Subgroup.card_dvd_of_le (c1aPcoreIn_le_fittingIn q B.U)),
        Nat.card_pos.ne'⟩
    rcases hqr with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · -- `s` inverts `O_q(U)`, `s₂` does not: take `t₁ = s₂`, `t₂ = s`
      have hdisj2 : pCoreIn q B.U ⊓ Is2 = ⊥ := by
        rcases hIs2dich q hq with h | h
        · exact absurd h hB
        · exact h
      refine ⟨⟨s2, s, q, hq, hs2S, hsS, hs2S0, hsS0, hs2ord, hsord, hpmem, ?_, ?_⟩⟩
      · exact hIs2cent q hq hdisj2
      · exact hIsinv q hq hA
    · -- `s₂` inverts `O_q(U)`, `s` does not: take `t₁ = s`, `t₂ = s₂`
      have hdisj : pCoreIn q B.U ⊓ Is = ⊥ := by
        rcases hIsdich q hq with h | h
        · exact absurd h hB
        · exact h
      refine ⟨⟨s, s2, q, hq, hsS, hs2S, hsS0, hs2S0, hsord, hs2ord, hpmem, ?_, ?_⟩⟩
      · exact hIscent q hq hdisj
      · exact hIs2inv q hq hA
  · -- ### Case B: the two reflections behave identically; then `S₀ ≤ C_G(U)`, contradicting
    -- Lemma 2.2
    push_neg at hcase
    have hiff : ∀ q : ℕ, q.Prime → (pCoreIn q B.U ≤ Is ↔ pCoreIn q B.U ≤ Is2) :=
      fun q hq => ⟨(hcase q hq).1, (hcase q hq).2⟩
    have hgcent : ∀ q : ℕ, q.Prime → pCoreIn q B.U ≤ Subgroup.centralizer ({g} : Set G) := by
      intro q hq
      haveI : Fact q.Prime := ⟨hq⟩
      by_cases hO : pCoreIn q B.U ≤ Is
      · -- both reflections invert `O_q(U)`, hence so does neither `g` nor its inverse: `g`
        -- centralizes
        have hO2 : pCoreIn q B.U ≤ Is2 := (hiff q hq).mp hO
        intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        have hy1 : s * y * s⁻¹ = y⁻¹ := by
          have hmem : y ∈ (Is : Set G) := hO hy
          rw [hIsc] at hmem
          exact (CORE2A.mem_invSet.mp hmem).2
        have hy2 : s2 * y * s2⁻¹ = y⁻¹ := by
          have hmem : y ∈ (Is2 : Set G) := hO2 hy
          rw [hIs2c] at hmem
          exact (CORE2A.mem_invSet.mp hmem).2
        have hgy : g * y * g⁻¹ = y := by
          rw [hgs]
          calc (s * s2) * y * (s * s2)⁻¹ = s * (s2 * y * s2⁻¹) * s⁻¹ := by group
            _ = s * y⁻¹ * s⁻¹ := by rw [hy2]
            _ = y := by
                  rw [show s * y⁻¹ * s⁻¹ = (s * y * s⁻¹)⁻¹ from by group, hy1, inv_inv]
        calc g * y = (g * y * g⁻¹) * g := by group
          _ = y * g := by rw [hgy]
      · -- neither reflection inverts `O_q(U)`, so both centralize it, hence `g` does
        have hO2 : ¬ (pCoreIn q B.U ≤ Is2) := fun hle => hO ((hiff q hq).mpr hle)
        have hdisj : pCoreIn q B.U ⊓ Is = ⊥ := by
          rcases hIsdich q hq with h | h
          · exact absurd h hO
          · exact h
        have hdisj2 : pCoreIn q B.U ⊓ Is2 = ⊥ := by
          rcases hIs2dich q hq with h | h
          · exact absurd h hO2
          · exact h
        have hcs : pCoreIn q B.U ≤ Subgroup.centralizer ({s} : Set G) := hIscent q hq hdisj
        have hcs2 : pCoreIn q B.U ≤ Subgroup.centralizer ({s2} : Set G) := hIs2cent q hq hdisj2
        intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        have hys : s * y * s⁻¹ = y := by
          have hcomm' := (Subgroup.mem_centralizer_iff.mp (hcs hy)) s (by simp)
          calc s * y * s⁻¹ = (s * y) * s⁻¹ := by group
            _ = (y * s) * s⁻¹ := by rw [hcomm']
            _ = y := by group
        have hys2 : s2 * y * s2⁻¹ = y := by
          have hcomm' := (Subgroup.mem_centralizer_iff.mp (hcs2 hy)) s2 (by simp)
          calc s2 * y * s2⁻¹ = (s2 * y) * s2⁻¹ := by group
            _ = (y * s2) * s2⁻¹ := by rw [hcomm']
            _ = y := by group
        have hgy : g * y * g⁻¹ = y := by
          rw [hgs]
          calc (s * s2) * y * (s * s2)⁻¹ = s * (s2 * y * s2⁻¹) * s⁻¹ := by group
            _ = s * y * s⁻¹ := by rw [hys2]
            _ = y := hys
        calc g * y = (g * y * g⁻¹) * g := by group
          _ = y * g := by rw [hgy]
    -- `g` centralizes `F(U)`, i.e. `F(U) ≤ C_G(⟨g⟩) = C_G(S₀)`
    have hF_le_C : fittingIn B.U ≤ Subgroup.centralizer ((B.S0 : Subgroup G) : Set G) := by
      rw [c1aFittingIn_eq_iSup_pCoreIn B.U]
      refine iSup_le fun p => ?_
      haveI : Fact p.val.Prime := ⟨p.2⟩
      rw [hS0zp, CORE2A.centralizer_zpowers_eq_singleton g]
      exact hgcent p.val p.2
    have hS0F : B.S0 ≤ Subgroup.centralizer ((fittingIn B.U : Subgroup G) : Set G) :=
      Subgroup.le_centralizer_iff.mpr hF_le_C
    -- `F(U) ⊴ U`
    have hFU_normal : B.U ≤ Subgroup.normalizer (fittingIn B.U : Set G) := by
      haveI hchar : (Work.GW2.fitting ↥B.U).Characteristic := c1aFitting_characteristic B.U
      have hN : (Work.GW2.fitting ↥B.U).Normal := inferInstance
      have h := c1aLe_normalizer_map_subtype (K := B.U) (N := Work.GW2.fitting ↥B.U) hN
      simpa [Work.GW2.fittingIn] using h
    -- `[S₀, U] ⊆ F(U)`
    have hcomm : ∀ h ∈ B.S0, ∀ u ∈ B.U, h * u * h⁻¹ * u⁻¹ ∈ fittingIn B.U := by
      intro h hh u hu
      -- write `h = s·y` with `y ∈ S − S₀`
      set y : G := s⁻¹ * h with hydef
      have hyS : y ∈ (B.S : Subgroup G) :=
        (B.S : Subgroup G).mul_mem ((B.S : Subgroup G).inv_mem hsS) (B.S0_le hh)
      have hyS0 : y ∉ B.S0 := by
        intro hymem
        refine hsS0 ?_
        have h1' : s⁻¹ = y * h⁻¹ := by rw [hydef]; group
        have hsinv : s⁻¹ ∈ B.S0 := by
          rw [h1']
          exact B.S0.mul_mem hymem (B.S0.inv_mem hh)
        simpa using B.S0.inv_mem hsinv
      have hyord : orderOf y = 2 := hrefl y hyS hyS0
      obtain ⟨Iy, hIyc, hIynorm, hIyleF, hIydich, hIycent, hIyinv⟩ := key y hyS hyS0 hyord
      have hy2 : y * y = 1 := by
        have h' : y ^ 2 = 1 := by rw [← hyord]; exact pow_orderOf_eq_one y
        simpa [pow_two] using h'
      have hyU : y ∈ Subgroup.normalizer (B.U : Set G) := CORE2A.bender_s_mem_normalizer_U B hyS
      have hsU : s ∈ Subgroup.normalizer (B.U : Set G) := CORE2A.bender_s_mem_normalizer_U B hsS
      -- the two `F(U)`-elements attached to `u`
      have hzy : u⁻¹ * (y * u * y⁻¹) ∈ fittingIn B.U := by
        refine hIyleF ?_
        show u⁻¹ * (y * u * y⁻¹) ∈ (Iy : Set G)
        rw [hIyc]
        exact CORE2A.mem_invSet.mpr ⟨B.U.mul_mem (B.U.inv_mem hu)
          ((Subgroup.mem_normalizer_iff.mp hyU u).mp hu), c1aInverted_of_sq_eq_one hy2⟩
      have hzx : u⁻¹ * (s * u * s⁻¹) ∈ fittingIn B.U := by
        refine hIsleF ?_
        show u⁻¹ * (s * u * s⁻¹) ∈ (Is : Set G)
        rw [hIsc]
        exact CORE2A.mem_invSet.mpr ⟨B.U.mul_mem (B.U.inv_mem hu)
          ((Subgroup.mem_normalizer_iff.mp hsU u).mp hu), c1aInverted_of_sq_eq_one hss⟩
      -- conjugation by `s` preserves `F(U)`
      have hFs : conjSub s (fittingIn B.U) = fittingIn B.U :=
        c1aConjSub_fittingIn_eq_self hsU
      have hsy : s * (u⁻¹ * (y * u * y⁻¹)) * s⁻¹ ∈ fittingIn B.U := by
        have hmem : s * (u⁻¹ * (y * u * y⁻¹)) * s⁻¹ ∈ conjSub s (fittingIn B.U) :=
          Subgroup.mem_map.mpr ⟨u⁻¹ * (y * u * y⁻¹), hzy, by simp [MulAut.conj_apply]⟩
        rwa [hFs] at hmem
      have hA : (u⁻¹ * (s * u * s⁻¹)) * (s * (u⁻¹ * (y * u * y⁻¹)) * s⁻¹) ∈ fittingIn B.U :=
        (fittingIn B.U).mul_mem hzx hsy
      have hconj : u * ((u⁻¹ * (s * u * s⁻¹)) * (s * (u⁻¹ * (y * u * y⁻¹)) * s⁻¹)) * u⁻¹
          ∈ fittingIn B.U :=
        ((Subgroup.mem_normalizer_iff.mp (hFU_normal hu))
          ((u⁻¹ * (s * u * s⁻¹)) * (s * (u⁻¹ * (y * u * y⁻¹)) * s⁻¹))).mp hA
      have hh_eq : h = s * y := by rw [hydef]; group
      have heq : h * u * h⁻¹ * u⁻¹
          = u * ((u⁻¹ * (s * u * s⁻¹)) * (s * (u⁻¹ * (y * u * y⁻¹)) * s⁻¹)) * u⁻¹ := by
        rw [hh_eq]
        calc (s * y) * u * (s * y)⁻¹ * u⁻¹
            = s * (y * u * y⁻¹) * s⁻¹ * u⁻¹ := by group
          _ = s * (u * (u⁻¹ * (y * u * y⁻¹))) * s⁻¹ * u⁻¹ := by
                rw [show u * (u⁻¹ * (y * u * y⁻¹)) = y * u * y⁻¹ from by group]
          _ = (s * u * s⁻¹) * (s * (u⁻¹ * (y * u * y⁻¹)) * s⁻¹) * u⁻¹ := by group
          _ = (u * (u⁻¹ * (s * u * s⁻¹))) *
                (s * (u⁻¹ * (y * u * y⁻¹)) * s⁻¹) * u⁻¹ := by
                rw [show u * (u⁻¹ * (s * u * s⁻¹)) = s * u * s⁻¹ from by group]
          _ = u * ((u⁻¹ * (s * u * s⁻¹)) *
                (s * (u⁻¹ * (y * u * y⁻¹)) * s⁻¹)) * u⁻¹ := by group
      rw [heq]
      exact hconj
    have hcomp_le : (⁅B.S0, B.U⁆ : Subgroup G) ≤ fittingIn B.U := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      exact hcomm a ha b hb
    -- Bender 1.1: `U = [S₀,U] · C_U(S₀)`
    have hUdecomp : (⁅B.S0, B.U⁆ : Subgroup G) ⊔
        (B.U ⊓ Subgroup.centralizer (B.S0 : Set G)) = B.U := by
      have hp : IsPGroup 2 (B.S0 : Subgroup G) := B.S.isPGroup'.to_le B.S0_le
      have hcp : Nat.Coprime 2 (Nat.card B.U) := Odd.coprime_two_left (CORE2A.bSetup_U_odd B)
      have hnorm : B.S0 ≤ Subgroup.normalizer (B.U : Set G) := fun x hx =>
        CORE2A.bender_s_mem_normalizer_U B (B.S0_le hx)
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact (I.T.c11i G 2 B.S0 B.U hp hcp hnorm).2
    have hUC : B.U ≤ Subgroup.centralizer ((B.S0 : Subgroup G) : Set G) := by
      rw [← hUdecomp]
      refine sup_le ?_ inf_le_right
      exact le_trans hcomp_le (Subgroup.le_centralizer_iff.mp hS0F)
    -- the configuration of Lemma 2.2 holds, contradicting `I.h22`
    have hS0C : B.S0 ≤ Subgroup.centralizer (B.U : Set G) :=
      Subgroup.le_centralizer_iff.mp hUC
    have hconfig : Lemma22Config B :=
      ⟨hS0C, s, hsS, hsS0, Is, hIsc, hIsnorm, fun X _ hXI => by
        rw [← hHhat]
        exact h1.2 X ‹X ≠ ⊥› (le_trans hXI hIsleF)⟩
    exact (I.h22 G I.T.ft hBc B hconfig).elim

end Work.CORE3

open Work.GW2

/-- The same theorem, exposed at the namespace of the file path (the skeleton's doubly nested
name `Work.CORE3.Work.CORE3.Case1aSetup` continues to exist unchanged). -/
theorem Case1aSetup (I : Case1Inputs) : Case1aSetupProp :=
  _root_.Work.CORE3.Work.CORE3.Case1aSetup I

end Work.CORE3
