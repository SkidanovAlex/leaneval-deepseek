import Mathlib
import Submission.Work.Hering.Perm.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Appendix II(5) of Peterfalvi I, p. 204

If `X` acts doubly transitively on a finite set `E` and `P` is a Sylow `p`-subgroup of the
two-point stabiliser of `a ≠ b`, then `N_X(P)` is doubly transitive on the set of points fixed
by `P`.

The mathematical content is:

* every point `c` fixed by `P` lies in the two-point stabiliser `X_a ⊓ X_c`, of which `P` is
  again a Sylow `p`-subgroup (it is a conjugate of `X_a ⊓ X_b`, since `X` is doubly transitive);
* hence, by Sylow conjugacy inside `X_a ⊓ X_b`, `P` and its conjugates are conjugate *inside*
  `X_a ⊓ X_b`, which produces elements of `N_X(P)` moving `b` to any other fixed point of `P`
  and swapping `a` and `b`;
* these two elements generate the required double transitivity on the fixed points.
-/

set_option autoImplicit false

namespace Work.Hering.Perm

open Work.Hering

/-- If `Q = k P k⁻¹` and `Q = h⁻¹ P h` then `h * k ∈ N(P)`.
Indeed `h k P (h k)⁻¹ = h (k P k⁻¹) h⁻¹ = h Q h⁻¹ = P`. -/
private lemma mem_normalizer_mul_of_map_conj_eq {X : Type*} [Group X] (P Q : Subgroup X) (h k : X)
    (hk : Q = P.map (MulAut.conj k).toMonoidHom)
    (hQ : Q = P.map (MulAut.conj h⁻¹).toMonoidHom) :
    h * k ∈ Subgroup.normalizer (P : Set X) := by
  have hQmem : ∀ z : X, z ∈ Q ↔ h * z * h⁻¹ ∈ P := by
    intro z
    rw [hQ, Subgroup.mem_map]
    constructor
    · rintro ⟨p, hp, hpz⟩
      have hpz' : h⁻¹ * p * h = z := by simpa [MulAut.conj_apply] using hpz
      rw [← hpz']
      have hh : h * (h⁻¹ * p * h) * h⁻¹ = p := by group
      rwa [hh]
    · intro hz
      refine ⟨h * z * h⁻¹, hz, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hkmem : ∀ z : X, z ∈ Q ↔ k⁻¹ * z * k ∈ P := by
    intro z
    rw [hk, Subgroup.mem_map]
    constructor
    · rintro ⟨p, hp, hpz⟩
      have hpz' : k * p * k⁻¹ = z := by simpa [MulAut.conj_apply] using hpz
      rw [← hpz']
      have hh : k⁻¹ * (k * p * k⁻¹) * k = p := by group
      rwa [hh]
    · intro hz
      refine ⟨k⁻¹ * z * k, hz, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  rw [Subgroup.mem_normalizer_iff'']
  intro y
  have key : h * (h⁻¹ * y * h) * h⁻¹ ∈ P ↔ k⁻¹ * (h⁻¹ * y * h) * k ∈ P := by
    rw [← hQmem, hkmem]
  have e1 : h * (h⁻¹ * y * h) * h⁻¹ = y := by group
  have e2 : k⁻¹ * (h⁻¹ * y * h) * k = (h * k)⁻¹ * y * (h * k) := by group
  rw [e1, e2] at key
  exact key

/-- **Sylow conjugacy inside a subgroup.** If `P ≤ K` is a maximal `p`-subgroup of `K` and
`Q ≤ K` is a `p`-subgroup of the same order, then `Q = k P k⁻¹` for some `k ∈ K`. -/
private lemma sylow_conj_aux {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {K P Q : Subgroup X} (hP : IsSylowSubgroup p P K) (hQK : Q ≤ K) (hQ : IsPGroup p ↥Q)
    (hcard : Nat.card ↥Q = Nat.card ↥P) :
    ∃ k ∈ K, Q = P.map (MulAut.conj k).toMonoidHom := by
  have hfact : Fact p.Prime := ⟨hp⟩
  obtain ⟨hPK, hPp, hPmax⟩ := hP
  -- `P` is also a maximal `p`-subgroup of the group `↥K`
  have hSPmax : ∀ {R : Subgroup ↥K}, IsPGroup p ↥R → P.subgroupOf K ≤ R → R = P.subgroupOf K := by
    intro R hRp hle
    refine le_antisymm ?_ hle
    intro y hy
    have hmem : ((y : X)) ∈ R.map K.subtype := ⟨y, hy, rfl⟩
    have hPle : P ≤ R.map K.subtype := by
      intro x hx
      have hxK : x ∈ K := hPK hx
      exact ⟨⟨x, hxK⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    have hleK : R.map K.subtype ≤ K := by
      rintro x ⟨y, -, rfl⟩
      exact y.2
    rw [hPmax (R.map K.subtype) hPle hleK (hRp.map K.subtype)] at hmem
    exact hmem
  let SP : Sylow p ↥K :=
    { toSubgroup := P.subgroupOf K
      isPGroup' := IsPGroup.of_equiv hPp (Subgroup.subgroupOfEquivOfLe hPK).symm
      is_maximal' := fun hR hle => hSPmax hR hle }
  have hSPcoe : (SP : Subgroup ↥K) = P.subgroupOf K := rfl
  have hQp' : IsPGroup p ↥(Q.subgroupOf K) :=
    IsPGroup.of_equiv hQ (Subgroup.subgroupOfEquivOfLe hQK).symm
  obtain ⟨T, hTle⟩ := IsPGroup.exists_le_sylow (p := p) hQp'
  have hfin : Finite (Sylow p ↥K) := Sylow.finite_of_finiteIndex SP
  -- Sylow's theorem: `T` is a conjugate of `SP` in `↥K`
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (↥K) SP T
  have hcardT : Nat.card ↥(T : Subgroup ↥K) = Nat.card ↥(SP : Subgroup ↥K) := by
    rw [Sylow.card_eq_multiplicity T, Sylow.card_eq_multiplicity SP]
  have hcardP : Nat.card ↥(SP : Subgroup ↥K) = Nat.card ↥P := by
    show Nat.card ↥(P.subgroupOf K) = Nat.card ↥P
    have h := Subgroup.card_map_of_injective (f := K.subtype)
      (Subtype.coe_injective : Function.Injective (K.subtype)) (K := P.subgroupOf K)
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPK] at h
    exact h.symm
  have hcardQ : Nat.card ↥(Q.subgroupOf K) = Nat.card ↥Q := by
    have h := Subgroup.card_map_of_injective (f := K.subtype)
      (Subtype.coe_injective : Function.Injective (K.subtype)) (K := Q.subgroupOf K)
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQK] at h
    exact h.symm
  -- `Q` has the order of a Sylow `p`-subgroup of `↥K`, so `Q.subgroupOf K = T`
  have hTQ : T = Q.subgroupOf K := by
    refine (Subgroup.eq_of_le_of_card_ge hTle ?_).symm
    rw [hcardT, hcardP, ← hcard, ← hcardQ]
  have h1 : ((k • SP : Sylow p ↥K) : Subgroup ↥K)
      = (SP : Subgroup ↥K).map (MulAut.conj k).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    congr 1
  have h2 : (P.subgroupOf K).map (MulAut.conj k).toMonoidHom = Q.subgroupOf K := by
    rw [← hSPcoe, ← h1, hk, hTQ]
  -- pass from subgroups of `↥K` back to subgroups of `X`
  have h3 : P.map (MulAut.conj (k : X)).toMonoidHom = Q := by
    have h4 := congrArg (Subgroup.map K.subtype) h2
    have hcomp : K.subtype.comp (MulAut.conj k).toMonoidHom
        = (MulAut.conj (k : X)).toMonoidHom.comp K.subtype := by
      ext x
      rfl
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map] at h4
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPK] at h4
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQK] at h4
    exact h4
  exact ⟨(k : X), k.2, h3.symm⟩

theorem appII5 : AppII5Prop := by
  intro X E hG hM hFX hFE h2 p hp a b hab P hP
  have hfact2 : Fact p.Prime := ⟨hp⟩
  -- Sylow conjugacy inside the two-point stabiliser (delegated as `Work.Hering.Perm.sylow_conj`)
  have sylowConj : ∀ {K P Q : Subgroup X},
      IsSylowSubgroup p P K → Q ≤ K → IsPGroup p ↥Q → Nat.card ↥Q = Nat.card ↥P →
      ∃ k ∈ K, Q = P.map (MulAut.conj k).toMonoidHom := by
    intro K P Q hP' hQK hQ hcard
    exact sylow_conj_aux hp hP' hQK hQ hcard
  have hPK : P ≤ MulAction.stabilizer X a ⊓ MulAction.stabilizer X b := hP.1
  have hPp : IsPGroup p ↥P := hP.2.1
  have hfix_a : ∀ x ∈ P, x • a = a := fun x hx => MulAction.mem_stabilizer_iff.mp (hPK hx).1
  have hfix_b : ∀ x ∈ P, x • b = b := fun x hx => MulAction.mem_stabilizer_iff.mp (hPK hx).2
  -- moving `b` to any other point fixed by `P`, fixing `a`
  have moveB : ∀ c : E, (∀ x ∈ P, x • c = c) → c ≠ a →
      ∃ n ∈ Subgroup.normalizer (P : Set X), n • a = a ∧ n • b = c := by
    intro c hc hca
    obtain ⟨h, hha, hhb⟩ := h2 a b a c hab (Ne.symm hca)
    have hia : h⁻¹ • a = a := by simpa [hha] using inv_smul_smul h a
    have hic : h⁻¹ • c = b := by rw [← hhb, inv_smul_smul]
    set Q : Subgroup X := P.map (MulAut.conj h⁻¹).toMonoidHom with hQdef
    have hQK : Q ≤ MulAction.stabilizer X a ⊓ MulAction.stabilizer X b := by
      intro x hx
      obtain ⟨y, hyP, hyx⟩ := Subgroup.mem_map.mp hx
      have hyx' : h⁻¹ * y * h = x := by simpa [MulAut.conj_apply] using hyx
      rw [Subgroup.mem_inf]
      constructor
      · rw [MulAction.mem_stabilizer_iff, ← hyx', mul_smul, mul_smul, hha, hfix_a y hyP, hia]
      · rw [MulAction.mem_stabilizer_iff, ← hyx', mul_smul, mul_smul, hhb, hc y hyP, hic]
    have hQp : IsPGroup p ↥Q := by
      rw [hQdef]
      exact hPp.map (MulAut.conj h⁻¹).toMonoidHom
    have hcard : Nat.card ↥Q = Nat.card ↥P := by
      rw [hQdef]
      exact Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj h⁻¹))
    obtain ⟨k, hkK, hk⟩ := sylowConj (K := _) (P := P) (Q := Q) hP hQK hQp hcard
    have hka : k • a = a := MulAction.mem_stabilizer_iff.mp hkK.1
    have hkb : k • b = b := MulAction.mem_stabilizer_iff.mp hkK.2
    exact ⟨h * k, mem_normalizer_mul_of_map_conj_eq P Q h k hk hQdef,
      by rw [mul_smul, hka, hha], by rw [mul_smul, hkb, hhb]⟩
  -- an element of `N_X(P)` swapping `a` and `b`
  have swapEl : ∃ n ∈ Subgroup.normalizer (P : Set X), n • a = b ∧ n • b = a := by
    obtain ⟨g, hga, hgb⟩ := h2 a b b a hab hab.symm
    have hgia : g⁻¹ • a = b := by rw [← hgb, inv_smul_smul]
    have hgib : g⁻¹ • b = a := by rw [← hga, inv_smul_smul]
    set Q : Subgroup X := P.map (MulAut.conj g).toMonoidHom with hQdef
    have hQK : Q ≤ MulAction.stabilizer X a ⊓ MulAction.stabilizer X b := by
      intro x hx
      obtain ⟨y, hyP, hyx⟩ := Subgroup.mem_map.mp hx
      have hyx' : g * y * g⁻¹ = x := by simpa [MulAut.conj_apply] using hyx
      rw [Subgroup.mem_inf]
      constructor
      · rw [MulAction.mem_stabilizer_iff, ← hyx', mul_smul, mul_smul, hgia, hfix_b y hyP, hgb]
      · rw [MulAction.mem_stabilizer_iff, ← hyx', mul_smul, mul_smul, hgib, hfix_a y hyP, hga]
    have hQp : IsPGroup p ↥Q := by
      rw [hQdef]
      exact hPp.map (MulAut.conj g).toMonoidHom
    have hcard : Nat.card ↥Q = Nat.card ↥P := by
      rw [hQdef]
      exact Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g))
    obtain ⟨k, hkK, hk⟩ := sylowConj (K := _) (P := P) (Q := Q) hP hQK hQp hcard
    have hka : k • a = a := MulAction.mem_stabilizer_iff.mp hkK.1
    have hkb : k • b = b := MulAction.mem_stabilizer_iff.mp hkK.2
    refine ⟨g⁻¹ * k, ?_, by rw [mul_smul, hka, hgia], by rw [mul_smul, hkb, hgib]⟩
    refine mem_normalizer_mul_of_map_conj_eq P Q g⁻¹ k hk ?_
    simpa using hQdef
  -- every point fixed by `P` is moved to `a` by some element of `N_X(P)`
  have toA : ∀ c : E, (∀ x ∈ P, x • c = c) → ∃ n ∈ Subgroup.normalizer (P : Set X), n • c = a := by
    intro c hc
    by_cases hca : c = a
    · exact ⟨1, one_mem _, by rw [hca, one_smul]⟩
    · obtain ⟨n, hnN, hna, hnb⟩ := moveB c hc hca
      obtain ⟨s, hsN, hsa, hsb⟩ := swapEl
      have hnc : n⁻¹ • c = b := by rw [← hnb, inv_smul_smul]
      exact ⟨s * n⁻¹, mul_mem hsN (inv_mem hnN), by rw [mul_smul, hnc, hsb]⟩
  -- `N_X(P)` preserves the set of points fixed by `P`
  have hpres : ∀ n ∈ Subgroup.normalizer (P : Set X), ∀ c : E, (∀ x ∈ P, x • c = c) →
      ∀ x ∈ P, x • (n • c) = n • c := by
    intro n hn c hc x hx
    have hconj : n⁻¹ * x * n ∈ P := (Subgroup.mem_normalizer_iff''.mp hn x).mp hx
    rw [← mul_smul, show x * n = n * (n⁻¹ * x * n) by group, mul_smul, hc _ hconj]
  intro c d c' d' hcp hdp hc'p hd'p hcd hc'd'
  -- map `(c, d)` to `(a, b)` inside `N_X(P)`
  obtain ⟨m₁, hm₁N, hm₁c⟩ := toA c hcp
  have hmd : ∀ x ∈ P, x • (m₁ • d) = m₁ • d := hpres m₁ hm₁N d hdp
  have hne : m₁ • d ≠ a := by
    intro hcon
    have h1 : m₁ • c = m₁ • d := by rw [hm₁c, hcon]
    have h2 : c = d := by
      have h3 := congrArg (fun z => m₁⁻¹ • z) h1
      simpa [smul_smul] using h3
    exact hcd h2
  obtain ⟨n₁, hn₁N, hn₁a, hn₁b⟩ := moveB (m₁ • d) hmd hne
  have hyc : (n₁⁻¹ * m₁) • c = a := by
    have h1 : n₁⁻¹ • a = a := by simpa [hn₁a] using inv_smul_smul n₁ a
    rw [mul_smul, hm₁c, h1]
  have hyd : (n₁⁻¹ * m₁) • d = b := by rw [mul_smul, ← hn₁b, inv_smul_smul]
  have hyN : (n₁⁻¹ * m₁) ∈ Subgroup.normalizer (P : Set X) := mul_mem (inv_mem hn₁N) hm₁N
  -- map `(c', d')` to `(a, b)` inside `N_X(P)`
  obtain ⟨m₂, hm₂N, hm₂c'⟩ := toA c' hc'p
  have hmd' : ∀ x ∈ P, x • (m₂ • d') = m₂ • d' := hpres m₂ hm₂N d' hd'p
  have hne' : m₂ • d' ≠ a := by
    intro hcon
    have h1 : m₂ • c' = m₂ • d' := by rw [hm₂c', hcon]
    have h2 : c' = d' := by
      have h3 := congrArg (fun z => m₂⁻¹ • z) h1
      simpa [smul_smul] using h3
    exact hc'd' h2
  obtain ⟨n₂, hn₂N, hn₂a, hn₂b⟩ := moveB (m₂ • d') hmd' hne'
  have hyc' : (n₂⁻¹ * m₂) • c' = a := by
    have h1 : n₂⁻¹ • a = a := by simpa [hn₂a] using inv_smul_smul n₂ a
    rw [mul_smul, hm₂c', h1]
  have hyd' : (n₂⁻¹ * m₂) • d' = b := by rw [mul_smul, ← hn₂b, inv_smul_smul]
  have hyN' : (n₂⁻¹ * m₂) ∈ Subgroup.normalizer (P : Set X) := mul_mem (inv_mem hn₂N) hm₂N
  have hfina : (n₂⁻¹ * m₂)⁻¹ • a = c' := by rw [← hyc', inv_smul_smul]
  have hfinb : (n₂⁻¹ * m₂)⁻¹ • b = d' := by rw [← hyd', inv_smul_smul]
  refine ⟨(n₂⁻¹ * m₂)⁻¹ * (n₁⁻¹ * m₁), mul_mem (inv_mem hyN') hyN, ?_, ?_⟩
  · rw [mul_smul, hyc, hfina]
  · rw [mul_smul, hyd, hfinb]

end Work.Hering.Perm
