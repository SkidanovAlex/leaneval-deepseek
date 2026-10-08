import Mathlib
import Submission.Work.Higman.Q3.Defs
import Submission.Work.Higman.cocycle_setup
import Submission.Work.Higman.Q3.card_irreducible
import Submission.Work.Higman.twoStep_q2_normal_form
import Submission.Work.Higman.Q3.cocycle_diagonal_pinning
import Submission.Work.Higman.exists_singer_iso
import Submission.Work.Higman.Q3.L12.q2xi_basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3.L12

open Work.Higman

/-! ## Helper lemmas -/

/-- **Singer coordinates on a `ξ`-invariant subgroup.**  If `U ≤ V` is invariant under the
additive automorphism `q2XiV` of `V`, has order `2 ^ n` and `q2XiV` permutes `U ∖ {0}`
transitively, then there is an additive isomorphism `U ≃+ 𝔽_{2^n}` intertwining `q2XiV` with
multiplication by a unit `ν` of order `2 ^ n - 1`. -/
theorem subgroup_singer_aux
    {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
    [Finite V] [Finite W] {b : V → V → W} [Biadd b]
    (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b))
    (U : AddSubgroup V) (hUinv : ∀ v : V, v ∈ U → q2XiV hcenter ξ v ∈ U)
    {n : ℕ} (hn : 2 ≤ n) (hUcard : Nat.card ↥U = 2 ^ n)
    (hUtrans : ∀ u : V, u ∈ U → u ≠ 0 → ∀ v : V, v ∈ U → v ≠ 0 →
      ∃ k : ℕ, ((q2XiV hcenter ξ : V → V)^[k]) u = v) :
    ∃ (φ : ↥U ≃+ GaloisField 2 n) (ν : (GaloisField 2 n)ˣ),
      orderOf ν = 2 ^ n - 1 ∧
      (∀ u : ↥U, φ ⟨q2XiV hcenter ξ (u : V), hUinv (u : V) u.2⟩ =
        (ν : GaloisField 2 n) * φ u) := by
  classical
  letI : Module (ZMod 2) V :=
    AddCommGroup.zmodModule fun z => by rw [two_nsmul]; exact AddExpTwo.add_self z
  haveI hUexp : AddExpTwo ↥U := ⟨fun x => by
    apply Subtype.ext
    rw [AddSubgroup.coe_add, AddExpTwo.add_self, AddSubgroup.coe_zero]⟩
  -- the restriction of `q2XiV` to `U`
  have hinj : Function.Injective
      (fun u : ↥U => (⟨q2XiV hcenter ξ (u : V), hUinv (u : V) u.2⟩ : ↥U)) :=
    fun a c h => Subtype.ext ((q2XiV hcenter ξ).injective (congrArg Subtype.val h))
  let τ : ↥U ≃+ ↥U := AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun u : ↥U => ⟨q2XiV hcenter ξ (u : V), hUinv (u : V) u.2⟩)
      (fun a c => by ext; exact map_add (q2XiV hcenter ξ) (a : V) (c : V)))
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hτ_val : ∀ u : ↥U, ((τ u : ↥U) : V) = q2XiV hcenter ξ (u : V) := fun u => rfl
  let τl : ↥U ≃ₗ[ZMod 2] ↥U := AddEquiv.toLinearEquiv τ (fun r u => by
    have h : r = 0 ∨ r = 1 := by revert r; decide
    rcases h with h | h <;> simp [h, hτ_val])
  have hτl_val : ∀ u : ↥U, ((τl u : ↥U) : V) = q2XiV hcenter ξ (u : V) := fun u => rfl
  have hτpow : ∀ (k : ℕ) (u : ↥U),
      (((τl ^ k) u : ↥U) : V) = ((q2XiV hcenter ξ : V → V)^[k]) (u : V) := by
    intro k
    induction k with
    | zero => intro u; rfl
    | succ k ih =>
        intro u
        rw [pow_succ', LinearEquiv.mul_apply]
        show q2XiV hcenter ξ (((τl ^ k) u : ↥U) : V) =
          ((q2XiV hcenter ξ : V → V)^[k + 1]) (u : V)
        rw [ih u, Function.iterate_succ_apply']
  have htrans : ∀ a d : ↥U, a ≠ 0 → d ≠ 0 → ∃ k : ℕ, (τl ^ k) a = d := by
    intro a d ha hd
    obtain ⟨k, hk⟩ := hUtrans (a : V) a.2 (fun h => ha (Subtype.ext h)) (d : V) d.2
      (fun h => hd (Subtype.ext h))
    refine ⟨k, Subtype.ext ?_⟩
    rw [hτpow k a]
    exact hk
  have h2U : 2 ≤ Nat.card ↥U := by
    rw [hUcard]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have hord : orderOf τl = 2 ^ n - 1 := by
    rw [q2_orderOf_of_transitive_linear τl h2U htrans, hUcard]
  have hfree : ∀ v : ↥U, τl v = v → v = 0 := by
    intro v hv
    by_contra hne
    have hτ1 : τl = 1 := by
      apply LinearEquiv.ext
      intro d
      rcases eq_or_ne d 0 with hd | hd
      · rw [hd, map_zero]
        rfl
      · obtain ⟨k, hk⟩ := htrans v d hne hd
        calc τl d = τl ((τl ^ k) v) := by rw [hk]
          _ = (τl ^ (k + 1)) v := by rw [pow_succ', LinearEquiv.mul_apply]
          _ = (τl ^ k) (τl v) := by rw [pow_succ, LinearEquiv.mul_apply]
          _ = (τl ^ k) v := by rw [hv]
          _ = d := hk
    have h1 : orderOf τl = 1 := by rw [hτ1, orderOf_one]
    rw [hord] at h1
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn
    omega
  obtain ⟨φl, ν, hν, hφ⟩ :=
    exists_singer_iso (by omega : 0 < n) hUcard τl hord hfree
  refine ⟨φl.toAddEquiv, ν, hν, fun u => ?_⟩
  exact hφ u

/-- **Singer coordinates on `W = Z(P)`.**  The regular automorphism `ξ` of `TwoStep V W b` acts
on `W` through a Singer cycle: there are `n` with `|W| = 2 ^ n`, an additive isomorphism
`ψ : W ≃+ 𝔽_{2^n}` and a unit `lam` of order `2 ^ n - 1` with `ψ (ξ w) = lam * ψ w`. -/
theorem singer_W_iso_aux
    {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
    [Finite V] [Finite W] {b : V → V → W} [Biadd b]
    (hW : 4 ≤ Nat.card W)
    (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b)) (hord : orderOf ξ = Nat.card W - 1)
    (htrans : ∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y) :
    ∃ (n : ℕ) (ψ : W ≃+ GaloisField 2 n) (lam : (GaloisField 2 n)ˣ),
      Nat.card W = 2 ^ n ∧ 1 ≤ n ∧ orderOf lam = 2 ^ n - 1 ∧
      (∀ w : W, ψ (q2XiW hcenter ξ w) = (lam : GaloisField 2 n) * ψ w) := by
  classical
  letI : Module (ZMod 2) V :=
    AddCommGroup.zmodModule fun z => by rw [two_nsmul]; exact AddExpTwo.add_self z
  letI : Module (ZMod 2) W :=
    AddCommGroup.zmodModule fun z => by rw [two_nsmul]; exact AddExpTwo.add_self z
  obtain ⟨n, hnW⟩ := card_W_eq_two_pow hW
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso; rw [h] at hnW; simp at hnW; omega
    · exact h
  obtain ⟨hσord, hσfree⟩ := q2Sig_orderOf_and_free hcenter ξ hW hord htrans
  have hfree : ∀ w : W, q2Sig hcenter ξ w = w → w = 0 := by
    intro w hw
    by_contra hne
    have hdvd : (Nat.card W - 1) ∣ 1 := hσfree 1 w hne (by simpa using hw)
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega
  have hσord' : orderOf (q2Sig hcenter ξ) = 2 ^ n - 1 := by rw [hσord, hnW]
  obtain ⟨ψl, lam, hlam, hψ⟩ :=
    exists_singer_iso (by omega : 0 < n) hnW (q2Sig hcenter ξ) hσord' hfree
  refine ⟨n, ψl.toAddEquiv, lam, hnW, hn1, hlam, fun w => ?_⟩
  exact hψ w

/-- **The additive splitting `V ≃+ U × U'`.**  If `U, U' ≤ V` span `V` and meet in `⊥`, then the
(uniquely determined) decomposition of a vector as a sum of an element of `U` and one of `U'`
is an additive isomorphism. -/
theorem decomp_add_equiv_aux
    {V : Type} [AddCommGroup V] [AddExpTwo V]
    (U U' : AddSubgroup V)
    (hsum : ∀ v : V, ∃ u ∈ U, ∃ u' ∈ U', u + u' = v)
    (hdisj : U ⊓ U' = ⊥) :
    ∃ e : V ≃+ (↥U × ↥U'),
      (∀ v : V, ((e v).1 : V) + ((e v).2 : V) = v) ∧
      (∀ (v : V) (u : ↥U) (u' : ↥U'), (u : V) + (u' : V) = v →
        (e v).1 = u ∧ (e v).2 = u') := by
  classical
  have huniq : ∀ (v : V) (u₁ : ↥U) (u₁' : ↥U') (u₂ : ↥U) (u₂' : ↥U'),
      (u₁ : V) + (u₁' : V) = v → (u₂ : V) + (u₂' : V) = v → u₁ = u₂ ∧ u₁' = u₂' := by
    intro v u₁ u₁' u₂ u₂' h1 h2
    have hz : ((u₁ : V) + (u₂ : V)) + ((u₁' : V) + (u₂' : V)) = 0 := by
      have h12 : (u₁ : V) + (u₁' : V) = (u₂ : V) + (u₂' : V) := by rw [h1, h2]
      calc ((u₁ : V) + (u₂ : V)) + ((u₁' : V) + (u₂' : V))
          = ((u₁ : V) + (u₁' : V)) + ((u₂ : V) + (u₂' : V)) := by abel
        _ = ((u₂ : V) + (u₂' : V)) + ((u₂ : V) + (u₂' : V)) := by rw [h12]
        _ = 0 := AddExpTwo.add_self _
    have heq : (u₁ : V) + (u₂ : V) = (u₁' : V) + (u₂' : V) :=
      AddExpTwo.eq_of_add_eq_zero hz
    have hmem : (u₁ : V) + (u₂ : V) ∈ U ⊓ U' :=
      ⟨U.add_mem u₁.2 u₂.2, by rw [heq]; exact U'.add_mem u₁'.2 u₂'.2⟩
    have h0 : (u₁ : V) + (u₂ : V) = 0 := by
      have hmem' : (u₁ : V) + (u₂ : V) ∈ (⊥ : AddSubgroup V) := by
        rw [← hdisj]; exact hmem
      simpa using hmem'
    have h0' : (u₁' : V) + (u₂' : V) = 0 := by rw [← heq]; exact h0
    exact ⟨Subtype.ext (AddExpTwo.eq_of_add_eq_zero h0),
      Subtype.ext (AddExpTwo.eq_of_add_eq_zero h0')⟩
  have hdec : ∀ v : V, ∃ p : ↥U × ↥U', ((p.1 : ↥U) : V) + ((p.2 : ↥U') : V) = v := by
    intro v
    obtain ⟨u, hu, u', hu', huv⟩ := hsum v
    exact ⟨(⟨u, hu⟩, ⟨u', hu'⟩), huv⟩
  let dec : V → ↥U × ↥U' := fun v => Classical.choose (hdec v)
  have decspec : ∀ v : V, ((dec v).1 : V) + ((dec v).2 : V) = v :=
    fun v => Classical.choose_spec (hdec v)
  have decadd : ∀ v w : V, dec (v + w) = dec v + dec w := by
    intro v w
    have hv := decspec v
    have hw := decspec w
    have hsum' : ((((dec v).1 + (dec w).1 : ↥U)) : V) +
        ((((dec v).2 + (dec w).2 : ↥U')) : V) = v + w := by
      calc ((((dec v).1 + (dec w).1 : ↥U)) : V) + ((((dec v).2 + (dec w).2 : ↥U')) : V)
          = (((dec v).1 : V) + ((dec v).2 : V)) + (((dec w).1 : V) + ((dec w).2 : V)) := by
            rw [AddSubgroup.coe_add, AddSubgroup.coe_add]; abel
        _ = v + w := by rw [hv, hw]
    obtain ⟨h1, h2⟩ := huniq (v + w) (dec (v + w)).1 (dec (v + w)).2
      ((dec v).1 + (dec w).1) ((dec v).2 + (dec w).2) (decspec (v + w)) hsum'
    exact Prod.ext h1 h2
  have hinj : Function.Injective dec := by
    intro v w h
    have hv := decspec v
    have hw := decspec w
    rw [h] at hv
    exact hv.symm.trans hw
  have hsurj : Function.Surjective dec := by
    rintro ⟨u, u'⟩
    refine ⟨(u : V) + (u' : V), ?_⟩
    obtain ⟨h1, h2⟩ := huniq ((u : V) + (u' : V))
      (dec ((u : V) + (u' : V))).1 (dec ((u : V) + (u' : V))).2 u u'
      (decspec _) rfl
    exact Prod.ext h1 h2
  let f : V →+ ↥U × ↥U' := AddMonoidHom.mk' dec decadd
  let e : V ≃+ (↥U × ↥U') := AddEquiv.ofBijective f ⟨hinj, hsurj⟩
  exact ⟨e, fun v => decspec v, fun v u u' h => huniq v (e v).1 (e v).2 u u' (decspec v) h⟩

/-- **The pinned shape of the squaring form** (the eigenvalue-coordinate setup of Higman's
Lemma 12).

Given the `ξ`-eigen-decomposition `V = U ⊕ U'` (two `ξ`-invariant subgroups `U`, `U'` of order
`q = |W|` on which the regular automorphism `ξ` of order `q - 1` is transitive on the non-zero
elements), there are additive isomorphisms `φ : V ≃+ 𝔽_q × 𝔽_q`, `ψ : W ≃+ 𝔽_q`, units `ν`, `ν'`
of order `q - 1` (the eigenvalues of `ξ` on `U`, `U'`) and `λ` of order `q - 1` (its eigenvalue
on `W`), so that the squaring form `u ↦ b u u` becomes
`C α^a + C' β^{a'} + ∑_{k,l<n} e_{kl} α^{2^k} β^{2^l}` with `C, C' ≠ 0` and the resonance
condition `e_{kl} ≠ 0 ⟹ ν^{2^k} ν'^{2^l} = λ`.

This is `Work.Higman.Q3.cocycle_diagonal_pinning` applied in the eigen-coordinates: `ξ` acts on
`U` (resp. `U'`, resp. `W`) through a Singer cycle (`Work.Higman.exists_singer_iso`), and the
equivariance `b (ξu) (ξu) = ξ (b u u)` is `Work.Higman.q2Tau_quad`; the two axes are anisotropic
because `b` is anisotropic (`b v v ≠ 0` for `v ≠ 0`, which follows from `hinvol` and `hcenter`).
The analogous one-step statement is `Work.Higman.Q3.exists_pinned_eigenbasis` (still `sorry`),
which additionally assumes nothing about `U`, `U'` but imports `Submission.Work.Higman.Q3.induced`.

The module `Submission.Work.Higman.Q3.L12.q2xi_basic` (imported here) already contains the
order/freeness facts about `q2XiV`, `q2XiW` and their iterates that the proof needs. -/
theorem exists_pinned_form
    {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
    [Finite V] [Finite W]
    {b : V → V → W} [Biadd b]
    (hcardV : Nat.card V = Nat.card W ^ 2) (hW : 4 ≤ Nat.card W)
    (hinvol : ∀ x : TwoStep V W b, x ^ 2 = 1 → x ∈ Subgroup.center (TwoStep V W b))
    (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b)) (hord : orderOf ξ = Nat.card W - 1)
    (htrans : ∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y)
    (U U' : AddSubgroup V)
    (hUinv : ∀ v : V, v ∈ U → q2XiV hcenter ξ v ∈ U)
    (hU'inv : ∀ v : V, v ∈ U' → q2XiV hcenter ξ v ∈ U')
    (hsum : ∀ v : V, ∃ u ∈ U, ∃ u' ∈ U', u + u' = v)
    (hdisj : U ⊓ U' = ⊥)
    (hUcard : Nat.card ↥U = Nat.card W) (hU'card : Nat.card ↥U' = Nat.card W)
    (hUtrans : ∀ u : V, u ∈ U → u ≠ 0 → ∀ v : V, v ∈ U → v ≠ 0 →
      ∃ k : ℕ, ((q2XiV hcenter ξ : V → V)^[k]) u = v)
    (hU'trans : ∀ u : V, u ∈ U' → u ≠ 0 → ∀ v : V, v ∈ U' → v ≠ 0 →
      ∃ k : ℕ, ((q2XiV hcenter ξ : V → V)^[k]) u = v) :
    ∃ (n : ℕ) (φ : V ≃+ (GaloisField 2 n × GaloisField 2 n)) (ψ : W ≃+ GaloisField 2 n)
      (ν ν' lam : (GaloisField 2 n)ˣ) (a a' : ℕ) (C C' : GaloisField 2 n)
      (e : ℕ → ℕ → GaloisField 2 n),
      Nat.card W = 2 ^ n ∧ 1 ≤ n ∧
      orderOf ν = 2 ^ n - 1 ∧ orderOf ν' = 2 ^ n - 1 ∧ orderOf lam = 2 ^ n - 1 ∧
      C ≠ 0 ∧ C' ≠ 0 ∧ 1 ≤ a ∧ a ≤ 2 ^ n - 1 ∧ 1 ≤ a' ∧ a' ≤ 2 ^ n - 1 ∧
      (↑ν : GaloisField 2 n) ^ a = ↑lam ∧ (↑ν' : GaloisField 2 n) ^ a' = ↑lam ∧
      (∀ α : GaloisField 2 n, ψ (b (φ.symm (α, 0)) (φ.symm (α, 0))) = C * α ^ a) ∧
      (∀ β : GaloisField 2 n, ψ (b (φ.symm (0, β)) (φ.symm (0, β))) = C' * β ^ a') ∧
      (∀ k l : ℕ, e k l ≠ 0 →
        (↑ν : GaloisField 2 n) ^ (2 ^ k) * (↑ν' : GaloisField 2 n) ^ (2 ^ l) = ↑lam) ∧
      (∀ α β : GaloisField 2 n,
        ψ (b (φ.symm (α, β)) (φ.symm (α, β))) =
          C * α ^ a + C' * β ^ a' +
            ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, e k l * α ^ (2 ^ k) * β ^ (2 ^ l)) := by
  classical
  letI : Module (ZMod 2) V :=
    AddCommGroup.zmodModule fun z => by rw [two_nsmul]; exact AddExpTwo.add_self z
  letI : Module (ZMod 2) W :=
    AddCommGroup.zmodModule fun z => by rw [two_nsmul]; exact AddExpTwo.add_self z
  -- ## the `W`-Singer coordinates
  obtain ⟨n, ψ, lam, hnW, hn1, hlamord, hψ⟩ := singer_W_iso_aux hW hcenter ξ hord htrans
  have hn2 : 2 ≤ n := by
    have h4 : 2 ^ 2 ≤ 2 ^ n := by rw [← hnW]; omega
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
  -- ## the two axis charts
  obtain ⟨φU, ν, hνord, hνeq⟩ :=
    subgroup_singer_aux hcenter ξ U hUinv hn2 (hUcard.trans hnW) hUtrans
  obtain ⟨φU', ν', hν'ord, hν'eq⟩ :=
    subgroup_singer_aux hcenter ξ U' hU'inv hn2 (hU'card.trans hnW) hU'trans
  -- ## the splitting and the combined chart
  obtain ⟨e, hesum, heuniq⟩ := decomp_add_equiv_aux U U' hsum hdisj
  let φ : V ≃+ (GaloisField 2 n × GaloisField 2 n) := e.trans (AddEquiv.prodCongr φU φU')
  have hφ_apply : ∀ v : V, φ v = (φU (e v).1, φU' (e v).2) := fun v => rfl
  -- ## the equivariance of `φ`
  have hφxi : ∀ v : V, φ (q2XiV hcenter ξ v) =
      ((ν : GaloisField 2 n) * (φ v).1, (ν' : GaloisField 2 n) * (φ v).2) := by
    intro v
    have hsumU : (((⟨q2XiV hcenter ξ ((e v).1 : V), hUinv ((e v).1 : V) ((e v).1).2⟩ :
          ↥U) : V)) +
        (((⟨q2XiV hcenter ξ ((e v).2 : V), hU'inv ((e v).2 : V) ((e v).2).2⟩ :
          ↥U') : V)) = q2XiV hcenter ξ v := by
      rw [show (((⟨q2XiV hcenter ξ ((e v).1 : V), hUinv ((e v).1 : V) ((e v).1).2⟩ :
            ↥U) : V)) = q2XiV hcenter ξ ((e v).1 : V) from rfl,
        show (((⟨q2XiV hcenter ξ ((e v).2 : V), hU'inv ((e v).2 : V) ((e v).2).2⟩ :
            ↥U') : V)) = q2XiV hcenter ξ ((e v).2 : V) from rfl,
        ← map_add (q2XiV hcenter ξ), hesum v]
    have hUc : (e (q2XiV hcenter ξ v)).1 =
        ⟨q2XiV hcenter ξ ((e v).1 : V), hUinv ((e v).1 : V) ((e v).1).2⟩ :=
      (heuniq (q2XiV hcenter ξ v) _ _ hsumU).1
    have hU'c : (e (q2XiV hcenter ξ v)).2 =
        ⟨q2XiV hcenter ξ ((e v).2 : V), hU'inv ((e v).2 : V) ((e v).2).2⟩ :=
      (heuniq (q2XiV hcenter ξ v) _ _ hsumU).2
    rw [hφ_apply, hφ_apply, hUc, hU'c, hνeq (e v).1, hν'eq (e v).2]
  -- ## the transferred form
  let b' : (GaloisField 2 n × GaloisField 2 n) →
      (GaloisField 2 n × GaloisField 2 n) → GaloisField 2 n :=
    fun x y => ψ (b (φ.symm x) (φ.symm y))
  have hb'add1 : ∀ x x' y : GaloisField 2 n × GaloisField 2 n,
      b' (x + x') y = b' x y + b' x' y := by
    intro x x' y
    show ψ (b (φ.symm (x + x')) (φ.symm y)) =
      ψ (b (φ.symm x) (φ.symm y)) + ψ (b (φ.symm x') (φ.symm y))
    rw [map_add φ.symm x x', Biadd.add_left (b := b) (φ.symm x) (φ.symm x') (φ.symm y),
      map_add ψ]
  have hb'add2 : ∀ x y y' : GaloisField 2 n × GaloisField 2 n,
      b' x (y + y') = b' x y + b' x y' := by
    intro x y y'
    show ψ (b (φ.symm x) (φ.symm (y + y'))) =
      ψ (b (φ.symm x) (φ.symm y)) + ψ (b (φ.symm x) (φ.symm y'))
    rw [map_add φ.symm y y', Biadd.add_right (b := b) (φ.symm x) (φ.symm y) (φ.symm y'),
      map_add ψ]
  haveI : Biadd b' := ⟨hb'add1, hb'add2⟩
  -- ## the equivariance of `b'`
  have hφsymm : ∀ x : GaloisField 2 n × GaloisField 2 n,
      φ.symm ((ν : GaloisField 2 n) * x.1, (ν' : GaloisField 2 n) * x.2) =
        q2XiV hcenter ξ (φ.symm x) := by
    intro x
    apply φ.injective
    rw [AddEquiv.apply_symm_apply, hφxi, AddEquiv.apply_symm_apply]
  have heq : ∀ α β : GaloisField 2 n,
      b' ((ν : GaloisField 2 n) * α, (ν' : GaloisField 2 n) * β)
        ((ν : GaloisField 2 n) * α, (ν' : GaloisField 2 n) * β) =
      (lam : GaloisField 2 n) * b' (α, β) (α, β) := by
    intro α β
    show ψ (b (φ.symm ((ν : GaloisField 2 n) * α, (ν' : GaloisField 2 n) * β))
        (φ.symm ((ν : GaloisField 2 n) * α, (ν' : GaloisField 2 n) * β))) =
      (lam : GaloisField 2 n) * ψ (b (φ.symm (α, β)) (φ.symm (α, β)))
    rw [hφsymm (α, β), q2_xiV_quad hcenter ξ (φ.symm (α, β)), hψ]
  -- ## anisotropy on the two axes
  have hne1 : ∀ α : GaloisField 2 n, α ≠ 0 → b' (α, 0) (α, 0) ≠ 0 := by
    intro α hα
    show ψ (b (φ.symm (α, 0)) (φ.symm (α, 0))) ≠ 0
    have h2 : (e (φ.symm (α, 0))).2 = 0 := by
      have hcoe : (φ (φ.symm (α, 0))).2 = φU' ((e (φ.symm (α, 0))).2) := rfl
      apply φU'.injective
      rw [map_zero, ← hcoe, AddEquiv.apply_symm_apply]
    have hu : φ.symm (α, 0) ∈ U := by
      have h1 := hesum (φ.symm (α, 0))
      rw [h2, AddSubgroup.coe_zero, add_zero] at h1
      rw [← h1]
      exact (e (φ.symm (α, 0))).1.2
    have hne : φ.symm (α, 0) ≠ 0 := by
      intro h0
      have hthis : φ (φ.symm (α, 0)) = φ 0 := by rw [h0]
      rw [AddEquiv.apply_symm_apply, map_zero] at hthis
      exact hα (congrArg Prod.fst hthis)
    have hbsq : b (φ.symm (α, 0)) (φ.symm (α, 0)) ≠ 0 :=
      fun hb0 => hne ((b_self_eq_zero_iff hinvol hcenter (φ.symm (α, 0))).mp hb0)
    intro hcontra
    exact hbsq (ψ.injective (by rw [hcontra, map_zero]))
  have hne2 : ∀ β : GaloisField 2 n, β ≠ 0 → b' (0, β) (0, β) ≠ 0 := by
    intro β hβ
    show ψ (b (φ.symm (0, β)) (φ.symm (0, β))) ≠ 0
    have h1 : (e (φ.symm (0, β))).1 = 0 := by
      have hcoe : (φ (φ.symm (0, β))).1 = φU ((e (φ.symm (0, β))).1) := rfl
      apply φU.injective
      rw [map_zero, ← hcoe, AddEquiv.apply_symm_apply]
    have hu : φ.symm (0, β) ∈ U' := by
      have h2 := hesum (φ.symm (0, β))
      rw [h1, AddSubgroup.coe_zero, zero_add] at h2
      rw [← h2]
      exact (e (φ.symm (0, β))).2.2
    have hne : φ.symm (0, β) ≠ 0 := by
      intro h0
      have hthis : φ (φ.symm (0, β)) = φ 0 := by rw [h0]
      rw [AddEquiv.apply_symm_apply, map_zero] at hthis
      exact hβ (congrArg Prod.snd hthis)
    have hbsq : b (φ.symm (0, β)) (φ.symm (0, β)) ≠ 0 :=
      fun hb0 => hne ((b_self_eq_zero_iff hinvol hcenter (φ.symm (0, β))).mp hb0)
    intro hcontra
    exact hbsq (ψ.injective (by rw [hcontra, map_zero]))
  -- ## pinning
  obtain ⟨a, a', C, C', hC, hC', ha1, haq, ha'1, ha'q, haν, ha'ν, hfax, hfbx, ⟨e', hres, hexp⟩⟩ :=
    cocycle_diagonal_pinning hn1 b' hνord hν'ord hlamord heq hne1 hne2
  have haνf : (↑ν : GaloisField 2 n) ^ a = ↑lam :=
    (Units.val_pow_eq_pow_val ν a).symm.trans (congrArg Units.val haν)
  have ha'νf : (↑ν' : GaloisField 2 n) ^ a' = ↑lam :=
    (Units.val_pow_eq_pow_val ν' a').symm.trans (congrArg Units.val ha'ν)
  have hresf : ∀ k l : ℕ, e' k l ≠ 0 →
      (↑ν : GaloisField 2 n) ^ (2 ^ k) * (↑ν' : GaloisField 2 n) ^ (2 ^ l) = ↑lam := by
    intro k l hkl
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using congrArg Units.val (hres k l hkl)
  exact ⟨n, φ, ψ, ν, ν', lam, a, a', C, C', e', hnW, hn1, hνord, hν'ord, hlamord,
    hC, hC', ha1, haq, ha'1, ha'q, haνf, ha'νf, hfax, hfbx, hresf, hexp⟩

end Work.Higman.Q3.L12
