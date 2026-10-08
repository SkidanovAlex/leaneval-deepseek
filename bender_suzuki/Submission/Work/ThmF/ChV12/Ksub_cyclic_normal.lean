import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmF.ChV12.Q0sub_elementary
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.KsubSubgroupOfNormal
import Submission.Work.ThmF.Tools.appX
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.ZassenhausPSL2.ZData.t_conj_eq_inv
import Submission.Work.Fitting.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi II, Ch. V §1, Proposition 2: `K = J(D,t)` is a cyclic normal subgroup of `D`

In the split rank-one situation `H = Q ⋊ D` with `D = H ∩ Hᵗ = twoPoint H t` and `t` an
involution outside `H`, put

* `V = C_D(t) = centD H t`, `K = J(D,t) = Kset H t = {x ∈ D | t x t⁻¹ = x⁻¹}`, `K̄ = ⟨K⟩`,
* `W = C_V(K) = C_D(Inv H)` (`Work.ThmF.W`, identified with `C_D(Inv H)` by Ch. II §4 Prop. 4).

**Proposition 2 (Peterfalvi II, p. 240):** `K̄ = K` is a cyclic normal subgroup of `D`.

The proof follows the source.  `Q₀ = Inv(H) ∪ {1}` is an elementary abelian 2-group
(Ch. V §1 Prop. 1, `Work.ThmF.ChV12.Q0sub_elementary`), `D` acts on it faithfully and
transitively on `Q₀^#` with kernel `W = C_D(Inv H)`, so **Appendix X**
(`Work.ThmF.Tools.appX`, applied to `P = D/W`) gives that `A := F(P)` is cyclic, acts
fixed-point-freely on `Q₀`, and that `P' ≤ A`.  Since `P' ≤ A` (i.e. `P/A` abelian) and `A`
is inverted by the involution `τ` induced by `t` (Appendix I: `C_A(τ) = 1` because `V`
centralises an involution, Ch. II §4 Prop. 2), the set `J(τ) = {x | τ x = x⁻¹}` is a subgroup
(`metabelianInverted` below) and equals `A` by Fitting's theorem.  Hence the image `K̄` of `K`
in `P` equals `A`, and counting with `A` fixed-point-free on `Q₀^# = Inv(H)` and `K` acting
regularly on `Inv(H)` gives `|K| = |A|`, so `K = ⟨k⟩` is cyclic and `K = K̄`;
`K̄ ⊴ D` is Ch. I App. I (4) (`Work.ThmF.ChV12.KsubSubgroupOfNormal`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV12

open LeanEval.GroupTheory.Defs

/-! ## The auxiliary group-theoretic lemma

If `Γ` has odd order, `τ` is an involutory automorphism, `A ⊴ Γ` with `Γ/A` abelian and `τ`
inverting every element of `A`, then `J(τ) = {x | τ x = x⁻¹}` is an abelian normal subgroup
of `Γ` containing `A`.  (This is the `B/W` argument of Peterfalvi's proof of Prop. 2: the
preimage `B` of `J(Γ/A,τ)` is a subgroup in which `τ` acts as inversion, because conjugation
by `x ∈ B` has odd order and inverts the element `τ x · x ∈ A`.) -/

private theorem metabelianInverted {Γ : Type} [Group Γ] [Finite Γ] (τ : Γ ≃* Γ) (hτ : ∀ x, τ (τ x) = x)
    (hodd : Odd (Nat.card Γ)) (A : Subgroup Γ) (hAn : A.Normal)
    (hab : ∀ x y : Γ, x * y * x⁻¹ * y⁻¹ ∈ A) (hAJ : ∀ a ∈ A, τ a = a⁻¹) :
    ∃ J : Subgroup Γ, (J : Set Γ) = {x : Γ | τ x = x⁻¹} ∧ J.Normal ∧
      (∀ x ∈ J, ∀ y ∈ J, x * y = y * x) ∧ A ≤ J := by
  classical
  -- the quotient Γ/A is abelian
  have hcommA : ∀ x y : Γ ⧸ A, x * y = y * x := by
    intro x y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective A x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective A y
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    simpa [mul_inv_rev, mul_assoc] using hab b⁻¹ a⁻¹
  letI : CommGroup (Γ ⧸ A) := { (inferInstance : Group (Γ ⧸ A)) with mul_comm := hcommA }
  have key : ∀ x : Γ, τ x * x ∈ A →
      (QuotientGroup.mk' A) (τ x) * (QuotientGroup.mk' A) x = 1 := by
    intro x hx
    have h1 : (QuotientGroup.mk' A) (τ x * x) = 1 := (QuotientGroup.eq_one_iff (τ x * x)).mpr hx
    rwa [map_mul] at h1
  let B : Subgroup Γ :=
    { carrier := {x : Γ | τ x * x ∈ A}
      one_mem' := by
        show τ 1 * 1 ∈ A
        rw [map_one, one_mul]
        exact A.one_mem
      mul_mem' := by
        intro x y hx hy
        show τ (x * y) * (x * y) ∈ A
        have h1 := key x hx
        have h2 := key y hy
        have hgoal : (QuotientGroup.mk' A) (τ x) * (QuotientGroup.mk' A) (τ y)
            * ((QuotientGroup.mk' A) x * (QuotientGroup.mk' A) y) = 1 := by
          rw [show (QuotientGroup.mk' A) (τ x) * (QuotientGroup.mk' A) (τ y)
                * ((QuotientGroup.mk' A) x * (QuotientGroup.mk' A) y)
              = ((QuotientGroup.mk' A) (τ x) * (QuotientGroup.mk' A) x)
                * ((QuotientGroup.mk' A) (τ y) * (QuotientGroup.mk' A) y) from by ac_rfl]
          rw [h1, h2, mul_one]
        rw [← QuotientGroup.eq_one_iff (τ (x * y) * (x * y))]
        simp only [map_mul]
        exact hgoal
      inv_mem' := by
        intro x hx
        show τ x⁻¹ * x⁻¹ ∈ A
        rw [map_inv]
        have h1 : x * τ x ∈ A := by
          have h2 := hAn.conj_mem (τ x * x) hx x
          convert h2 using 1
          group
        have h3 : (x * τ x)⁻¹ ∈ A := A.inv_mem h1
        convert h3 using 1
        rw [mul_inv_rev] }
  -- B ⊆ {x | τ x = x⁻¹}
  have hBJ : ∀ x ∈ B, τ x = x⁻¹ := by
    intro x hx
    have huA : τ x * x ∈ A := hx
    have hvA : x * τ x ∈ A := by
      have h2 := hAn.conj_mem (τ x * x) huA x
      convert h2 using 1
      group
    have hτv : τ (x * τ x) = τ x * x := by
      rw [map_mul, hτ x]
    have huv : τ x * x = (x * τ x)⁻¹ := by
      rw [← hτv, hAJ (x * τ x) hvA]
    have huv' : (τ x * x)⁻¹ = x * τ x := by
      have h := congrArg (fun z : Γ => z⁻¹) huv
      simpa [inv_inv] using h
    have hconj_u : (MulAut.conj x) (τ x * x) = (τ x * x)⁻¹ := by
      rw [MulAut.conj_apply, huv']
      group
    have hpow : ∀ k : ℕ, ((MulAut.conj x) ^ k) (τ x * x) = (τ x * x) ^ ((-1 : ℤ) ^ k) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc ((MulAut.conj x) ^ (k + 1)) (τ x * x)
            = ((MulAut.conj x) ^ k) ((MulAut.conj x) (τ x * x)) := by
              rw [pow_succ, MulAut.mul_apply]
          _ = ((MulAut.conj x) ^ k) ((τ x * x)⁻¹) := by rw [hconj_u]
          _ = (((MulAut.conj x) ^ k) (τ x * x))⁻¹ := by rw [map_inv]
          _ = ((τ x * x) ^ ((-1 : ℤ) ^ k))⁻¹ := by rw [ih]
          _ = (τ x * x) ^ (-((-1 : ℤ) ^ k)) := by rw [zpow_neg]
          _ = (τ x * x) ^ ((-1 : ℤ) ^ (k + 1)) := by
              congr 1
              rw [pow_succ]
              ring
    have hn : ((MulAut.conj x) ^ (orderOf x)) = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have hodd_x : Odd (orderOf x) := Odd.of_dvd_nat hodd (orderOf_dvd_natCard x)
    have hfinal : τ x * x = 1 := by
      have h1 : (τ x * x) = (τ x * x) ^ ((-1 : ℤ) ^ (orderOf x)) := by
        rw [← hpow (orderOf x), hn]
        simp
      have h2 : (τ x * x) ^ ((-1 : ℤ) ^ (orderOf x)) = (τ x * x)⁻¹ := by
        rw [hodd_x.neg_one_pow, zpow_neg_one]
      have huu : τ x * x = (τ x * x)⁻¹ := by nth_rewrite 1 [h1]; exact h2
      have hsq : (τ x * x) * (τ x * x) = 1 := by
        nth_rewrite 2 [huu]
        rw [mul_inv_cancel]
      have hdvd2 : orderOf (τ x * x) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hsq)
      have hoddA : Odd (Nat.card ↥A) := by
        have hdvd : Nat.card ↥A ∣ Nat.card Γ := by
          have h1 := Subgroup.card_dvd_of_le (le_top : A ≤ (⊤ : Subgroup Γ))
          rwa [Subgroup.card_top] at h1
        exact Odd.of_dvd_nat hodd hdvd
      have hdvdA : orderOf (τ x * x) ∣ Nat.card ↥A := Subgroup.orderOf_dvd_natCard A huA
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
      · exact orderOf_eq_one_iff.mp h
      · exact absurd (Odd.of_dvd_nat hoddA hdvdA) (by rw [h]; exact Nat.not_odd_iff_even.mpr even_two)
    exact (mul_eq_one_iff_eq_inv).mp hfinal
  -- B = {x | τ x = x⁻¹}
  have hBset : (B : Set Γ) = {x : Γ | τ x = x⁻¹} := by
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      exact hBJ x hx
    · intro x hx
      show τ x * x ∈ A
      rw [hx, inv_mul_cancel]
      exact A.one_mem
  -- B is normal
  have hBnorm : B.Normal := by
    refine Subgroup.Normal.mk (fun n hn g => ?_)
    show τ (g * n * g⁻¹) * (g * n * g⁻¹) ∈ A
    have h1 : (QuotientGroup.mk' A) (τ n) * (QuotientGroup.mk' A) n = 1 := key n hn
    have hgoal : (QuotientGroup.mk' A) (τ g) * (QuotientGroup.mk' A) (τ n)
          * ((QuotientGroup.mk' A) (τ g))⁻¹
          * ((QuotientGroup.mk' A) g * (QuotientGroup.mk' A) n * ((QuotientGroup.mk' A) g)⁻¹)
        = 1 := by
      rw [show (QuotientGroup.mk' A) (τ g) * (QuotientGroup.mk' A) (τ n)
            * ((QuotientGroup.mk' A) (τ g))⁻¹
            * ((QuotientGroup.mk' A) g * (QuotientGroup.mk' A) n * ((QuotientGroup.mk' A) g)⁻¹)
          = ((QuotientGroup.mk' A) (τ n) * (QuotientGroup.mk' A) n)
            * ((QuotientGroup.mk' A) (τ g) * ((QuotientGroup.mk' A) (τ g))⁻¹)
            * ((QuotientGroup.mk' A) g * ((QuotientGroup.mk' A) g)⁻¹) from by ac_rfl]
      rw [h1, mul_inv_cancel, mul_one, mul_inv_cancel, mul_one]
    rw [← QuotientGroup.eq_one_iff (τ (g * n * g⁻¹) * (g * n * g⁻¹))]
    simp only [map_mul, map_inv]
    exact hgoal
  -- B is abelian
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    have hx' : τ x = x⁻¹ := hBJ x hx
    have hy' : τ y = y⁻¹ := hBJ y hy
    have hxy : τ (x * y) = (x * y)⁻¹ := hBJ (x * y) (B.mul_mem hx hy)
    rw [map_mul, hx', hy', mul_inv_rev] at hxy
    have h3 := congrArg (fun z : Γ => z⁻¹) hxy
    simpa [mul_inv_rev, inv_inv] using h3.symm
  exact ⟨B, hBset, hBnorm, hBcomm, fun a ha => by
    show τ a * a ∈ A
    rw [hAJ a ha, inv_mul_cancel]
    exact A.one_mem⟩

theorem Ksub_cyclic_normal {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hS : Submission.Blueprint.Situation G) (h : Submission.Blueprint.IsSplitRankOne H Q t) :
    IsCyclic ↥(Work.ThmF.Ksub H t) ∧ (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t ∧
      ((Work.ThmF.Ksub H t).subgroupOf (Submission.Blueprint.twoPoint H t)).Normal := by

  classical
  have hcomm := Work.ThmF.L5.involutions_commute hS hC4 h
  obtain ⟨hQ0sq, hQ0comm, hQ0norm, hQ0inv⟩ := Work.ThmF.ChV12.Q0sub_elementary H hcomm
  have hP4 := (hC4 G hS H h.stronglyEmbedded t h.invol h.not_mem).2.2.2.2.1
  have hP2a := (hC4 G hS H h.stronglyEmbedded t h.invol h.not_mem).2.1
  have hW_eq : Work.ThmF.W H t =
      Submission.Blueprint.twoPoint H t ⊓
        Subgroup.centralizer (Submission.Blueprint.involutions (H : Set G)) := by
    simpa only [Work.ThmF.W, Work.ThmF.Kset] using hP4
  have hW_le_D : Work.ThmF.W H t ≤ Submission.Blueprint.twoPoint H t := by
    rw [hW_eq]; exact inf_le_left
  -- W is normal in D
  have hWsub_normal : ((Work.ThmF.W H t).subgroupOf (Submission.Blueprint.twoPoint H t)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hW_le_D]
    intro w d hw hd
    rw [hW_eq] at hw ⊢
    obtain ⟨hwD, hwC⟩ := Subgroup.mem_inf.mp hw
    have hdH : d ∈ H := (Subgroup.mem_inf.mp hd).1
    refine Subgroup.mem_inf.mpr ⟨(Submission.Blueprint.twoPoint H t).mul_mem
      ((Submission.Blueprint.twoPoint H t).mul_mem hd hwD)
      ((Submission.Blueprint.twoPoint H t).inv_mem hd), ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hwC ⊢
    intro a ha
    have ha' : d⁻¹ * a * d ∈ Submission.Blueprint.involutions (H : Set G) := by
      refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hdH) ha.1) hdH, ?_⟩
      have h1 : d⁻¹ * a * d = (MulAut.conj d⁻¹) a := by rw [MulAut.conj_apply, inv_inv]
      rw [h1, MulEquiv.orderOf_eq, ha.2]
    have h2 := hwC (d⁻¹ * a * d) ha'
    calc a * (d * w * d⁻¹) = d * (d⁻¹ * a * d) * w * d⁻¹ := by group
      _ = d * ((d⁻¹ * a * d) * w) * d⁻¹ := by group
      _ = d * (w * (d⁻¹ * a * d)) * d⁻¹ := by rw [← h2]
      _ = (d * w * d⁻¹) * a := by group
  -- abbreviation for D
  set D : Subgroup G := Submission.Blueprint.twoPoint H t with hD
  have hDmem : ∀ d : ↥D, (d : G) ∈ Submission.Blueprint.twoPoint H t := fun d => hD ▸ d.2
  have hDmemH : ∀ d : ↥D, (d : G) ∈ H := fun d => (Subgroup.mem_inf.mp (hDmem d)).1
  have hW_le_D' : Work.ThmF.W H t ≤ D := by rw [hD]; exact hW_le_D
  haveI hWn : ((Work.ThmF.W H t).subgroupOf D).Normal := hWsub_normal
  -- the conjugation action of ↥D on Q0sub H
  have hQ0mem : ∀ d : ↥D, (d : G) ∈ Subgroup.normalizer (Work.ThmF.Q0sub H : Set G) := by
    intro d
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hQ0norm (d : G) (hDmemH d) x hx
    · intro hx
      have h1 := hQ0norm ((d : G)⁻¹) (H.inv_mem (hDmemH d)) ((d : G) * x * (d : G)⁻¹) hx
      have h2 : (d : G)⁻¹ * ((d : G) * x * (d : G)⁻¹) * (d : G)⁻¹⁻¹ = x := by group
      rwa [h2] at h1
  let incD : ↥D →* ↥(Subgroup.normalizer (Work.ThmF.Q0sub H : Set G)) :=
    { toFun := fun d => ⟨(d : G), hQ0mem d⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  let ψ : ↥D →* MulAut ↥(Work.ThmF.Q0sub H) :=
    (Subgroup.normalizerMonoidHom (Work.ThmF.Q0sub H)).comp incD
  have hψ_apply : ∀ (d : ↥D) (x : ↥(Work.ThmF.Q0sub H)),
      ((ψ d x : ↥(Work.ThmF.Q0sub H)) : G) = (d : G) * (x : G) * (d : G)⁻¹ := fun d x => rfl
  -- kernel of ψ is W
  have hker_ψ : ψ.ker = (Work.ThmF.W H t).subgroupOf D := by
    ext d
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hd
      have hfix : ∀ x : ↥(Work.ThmF.Q0sub H), ψ d x = x := fun x =>
        congrArg (fun f : MulAut ↥(Work.ThmF.Q0sub H) => f x) hd
      rw [hW_eq, Subgroup.mem_inf]
      refine ⟨hDmem d, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have haQ : a ∈ Work.ThmF.Q0sub H := Work.ThmF.Q0_le_Q0sub H (Or.inl ha)
      have h1 := hfix ⟨a, haQ⟩
      have h2 : (d : G) * a * (d : G)⁻¹ = a := by
        have := congrArg (fun z : ↥(Work.ThmF.Q0sub H) => (z : G)) h1
        rwa [hψ_apply] at this
      show a * (d : G) = (d : G) * a
      have h3 := congrArg (fun z => z * (d : G)) h2
      have h4 : (d : G) * a = a * (d : G) := by simpa [mul_assoc] using h3
      exact h4.symm
    · intro hd
      rw [hW_eq, Subgroup.mem_inf] at hd
      obtain ⟨hdD, hdC⟩ := hd
      refine MulEquiv.ext (fun x => ?_)
      show (ψ d) x = x
      apply Subtype.ext
      rw [hψ_apply]
      by_cases hx : (x : G) = 1
      · rw [hx]; simp
      · have hxin := hQ0inv (x : G) x.2 hx
        have hcx : (x : G) * (d : G) = (d : G) * (x : G) :=
          (Subgroup.mem_centralizer_iff.mp hdC) (x : G) hxin
        rw [← hcx, mul_assoc, mul_inv_cancel, mul_one]
  have hW_le_ker : (Work.ThmF.W H t).subgroupOf D ≤ ψ.ker := by rw [hker_ψ]
  -- P := D/W and the action ρ
  let P := ↥D ⧸ ((Work.ThmF.W H t).subgroupOf D)
  let ρ : P →* MulAut ↥(Work.ThmF.Q0sub H) :=
    QuotientGroup.lift ((Work.ThmF.W H t).subgroupOf D) ψ hW_le_ker
  have hρ_mk : ∀ (d : ↥D) (x : ↥(Work.ThmF.Q0sub H)),
      (ρ (QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D) d)) x = ψ d x := by
    intro d x
    change (QuotientGroup.lift ((Work.ThmF.W H t).subgroupOf D) ψ hW_le_ker
      (QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D) d)) x = ψ d x
    rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk']
  have hρ_inj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    show (QuotientGroup.lift ((Work.ThmF.W H t).subgroupOf D) ψ hW_le_ker).ker = ⊥
    rw [QuotientGroup.ker_lift, hker_ψ, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hP_odd : Odd (Nat.card P) := by
    have hdvd : Nat.card P ∣ Nat.card ↥D := by
      have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup
        ((Work.ThmF.W H t).subgroupOf D)
      rw [hc]
      exact dvd_mul_right _ _
    have hoddD : Odd (Nat.card ↥D) := by
      rw [hD]; exact Work.ThmF.split_odd_card_twoPoint h
    exact Odd.of_dvd_nat hoddD hdvd
  have hρ_trans : ∀ a b : ↥(Work.ThmF.Q0sub H), a ≠ 1 → b ≠ 1 → ∃ d : P, ρ d a = b := by
    intro a b ha hb
    have haG : (a : G) ≠ 1 := fun hh => ha (Subtype.ext hh)
    have hbG : (b : G) ≠ 1 := fun hh => hb (Subtype.ext hh)
    have ha' : (a : G) ∈ Submission.Blueprint.involutions (H : Set G) := hQ0inv (a : G) a.2 haG
    have hb' : (b : G) ∈ Submission.Blueprint.involutions (H : Set G) := hQ0inv (b : G) b.2 hbG
    obtain ⟨d, hd, hdab⟩ :=
      Work.ThmF.Bender.DTransitiveInv h.stronglyEmbedded h.invol h.not_mem (a : G) ha' (b : G) hb'
    refine ⟨QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D) ⟨d, by rw [hD]; exact hd⟩, ?_⟩
    rw [hρ_mk]
    apply Subtype.ext
    rw [hψ_apply]
    exact hdab
  -- App X
  have happX := Work.ThmF.Tools.appX hFT hP_odd Nat.prime_two
    (fun x y : ↥(Work.ThmF.Q0sub H) => Subtype.ext (hQ0comm (x : G) x.2 (y : G) y.2))
    (fun x : ↥(Work.ThmF.Q0sub H) => by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
      exact hQ0sq (x : G) x.2)
    ρ hρ_inj hρ_trans
  obtain ⟨hFcyc, hFfpf, hFcomm⟩ := happX

  -- t normalizes D, giving an involution tau on P
  have htD : t ∈ Subgroup.normalizer (D : Set G) := by
    rw [hD]; exact Work.ThmF.normalizes_twoPoint_of_data (Work.ThmF.IsSplitRankOne.toData h)
  have htD' : ∀ h : G, h ∈ D ↔ t * h * t⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp htD)
  have hconj_mem : ∀ d : ↥D, t * (d : G) * t⁻¹ ∈ D := fun d => (htD' (d : G)).mp d.2
  have htt : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rw [h.invol] at h1
    simpa [pow_two] using h1
  have htt' : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, htt, inv_one]
  let ctD : ↥D →* ↥D :=
    { toFun := fun d => ⟨t * (d : G) * t⁻¹, hconj_mem d⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show t * ((a : G) * (b : G)) * t⁻¹ = (t * (a : G) * t⁻¹) * (t * (b : G) * t⁻¹)
        group) }
  have hctD2 : ∀ d : ↥D, ctD (ctD d) = d := by
    intro d
    apply Subtype.ext
    show t * (t * (d : G) * t⁻¹) * t⁻¹ = (d : G)
    rw [show t * (t * (d : G) * t⁻¹) * t⁻¹ = (t * t) * (d : G) * (t⁻¹ * t⁻¹) by group,
      htt, htt']
    simp
  have hctD_apply : ∀ d : ↥D, ((ctD d : ↥D) : G) = t * (d : G) * t⁻¹ := fun d => rfl
  have hW_conj : ∀ w ∈ Work.ThmF.W H t, t * w * t⁻¹ = w := by
    intro w hw
    have hwV : w ∈ Submission.Blueprint.centD H t := Work.ThmF.W_le_centD H t hw
    have hc : t * w = w * t :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hwV).2 t (by simp)
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have hW_fix : ∀ d : ↥D, (d : G) ∈ Work.ThmF.W H t → ctD d = d := by
    intro d hd
    apply Subtype.ext
    rw [hctD_apply]
    exact hW_conj (d : G) hd
  have hcomap : (Work.ThmF.W H t).subgroupOf D
      ≤ Subgroup.comap ctD ((Work.ThmF.W H t).subgroupOf D) := by
    intro w hw
    rw [Subgroup.mem_comap]
    have hw' : (w : G) ∈ Work.ThmF.W H t := Subgroup.mem_subgroupOf.mp hw
    refine Subgroup.mem_subgroupOf.mpr ?_
    rw [hctD_apply, hW_conj (w : G) hw']
    exact hw'
  let τhom : P →* P := QuotientGroup.map ((Work.ThmF.W H t).subgroupOf D)
    ((Work.ThmF.W H t).subgroupOf D) ctD hcomap
  have hτhom_mk : ∀ d : ↥D, τhom (QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D) d)
      = QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D) (ctD d) :=
    fun d => QuotientGroup.map_mk' _ _ _ _ d
  have hτhom2 : ∀ x : P, τhom (τhom x) = x := by
    intro x
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective ((Work.ThmF.W H t).subgroupOf D) x
    rw [hτhom_mk, hτhom_mk]
    show QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D) (ctD (ctD d))
      = QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D) d
    rw [hctD2]
  have hτhom_bij : Function.Bijective τhom := by
    refine ⟨fun x y hxy => ?_, fun y => ⟨τhom y, hτhom2 y⟩⟩
    have h := congrArg τhom hxy
    rwa [hτhom2 x, hτhom2 y] at h
  let τ : P ≃* P := MulEquiv.ofBijective τhom hτhom_bij
  have hτ_mk : ∀ d : ↥D, τ (QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D) d)
      = QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D) (ctD d) := by
    intro d
    show τhom (QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D) d) = _
    exact hτhom_mk d
  have hτ2 : ∀ x : P, τ (τ x) = x := by
    intro x
    show τhom (τhom x) = x
    exact hτhom2 x
  -- centralizer of tau in P is the image of V
  have hCτ : ∀ d : ↥D, τ (QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D) d)
        = QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D) d
      ↔ (d : G) ∈ Submission.Blueprint.centD H t := by
    intro d
    rw [hτ_mk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    constructor
    · intro hmem
      have hcoe : (((ctD d)⁻¹ * d : ↥D) : G) = t * (d : G)⁻¹ * t⁻¹ * (d : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hctD_apply]
        group
      have hwW : t * (d : G)⁻¹ * t⁻¹ * (d : G) ∈ Work.ThmF.W H t := by
        rw [← hcoe]
        exact Subgroup.mem_subgroupOf.mp hmem
      set w : G := t * (d : G)⁻¹ * t⁻¹ * (d : G) with hw
      have hwt : t * w * t⁻¹ = w := by
        have hwV : w ∈ Submission.Blueprint.centD H t := Work.ThmF.W_le_centD H t hwW
        have hc : t * w = w * t :=
          Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hwV).2 t (by simp)
        rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      have hwt' : t * w⁻¹ * t⁻¹ = w⁻¹ := by
        rw [show t * w⁻¹ * t⁻¹ = (t * w * t⁻¹)⁻¹ by group, hwt]
      have h1 : (t * (d : G) * t⁻¹)⁻¹ = w * (d : G)⁻¹ := by
        have h0 : (t * (d : G) * t⁻¹)⁻¹ * (d : G) = w := by rw [hw]; group
        rw [← h0]
        group
      have htw : t * (d : G) * t⁻¹ = (d : G) * w⁻¹ := by
        have h3 := congrArg (fun z : G => z⁻¹) h1
        rw [inv_inv] at h3
        rw [mul_inv_rev, inv_inv] at h3
        exact h3
      have hd_eq : (d : G) = t * (t * (d : G) * t⁻¹) * t⁻¹ := by
        rw [show t * (t * (d : G) * t⁻¹) * t⁻¹ = (t * t) * (d : G) * (t⁻¹ * t⁻¹) by group,
          htt, htt']
        simp
      have hww : w * w = 1 := by
        have hstep : (d : G) = (d : G) * w⁻¹ * w⁻¹ := by
          calc (d : G) = t * (t * (d : G) * t⁻¹) * t⁻¹ := hd_eq
            _ = t * ((d : G) * w⁻¹) * t⁻¹ := by rw [htw]
            _ = (t * (d : G) * t⁻¹) * (t * w⁻¹ * t⁻¹) := by group
            _ = (d : G) * w⁻¹ * w⁻¹ := by rw [htw, hwt']
        have h5 : (d : G) * (w⁻¹ * w⁻¹) = (d : G) * 1 := by
          rw [mul_one, ← mul_assoc]
          exact hstep.symm
        have h6 : w⁻¹ * w⁻¹ = 1 := mul_left_cancel h5
        have h7 := congrArg (fun z : G => z⁻¹) h6
        simpa [mul_inv_rev, inv_inv] using h7
      have hw1 : w = 1 := by
        have hdvd : orderOf w ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hww)
        have hoddW : Odd (orderOf w) := by
          have hDodd : Odd (Nat.card ↥D) := by
            rw [hD]; exact Work.ThmF.split_odd_card_twoPoint h
          exact Odd.of_dvd_nat hDodd (Subgroup.orderOf_dvd_natCard D (hW_le_D' hwW))
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
        · exact orderOf_eq_one_iff.mp h1
        · exact absurd (h1 ▸ hoddW) (Nat.not_odd_iff_even.mpr even_two)
      have hdt : t * (d : G) * t⁻¹ = (d : G) := by
        rw [htw, hw1, inv_one, mul_one]
      refine Subgroup.mem_inf.mpr ⟨d.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h4 := congrArg (fun z => z * t) hdt
      simpa [mul_assoc] using h4.symm
    · intro hd
      rw [Subgroup.mem_subgroupOf]
      have hdt : t * (d : G) * t⁻¹ = (d : G) := by
        have hc : t * (d : G) = (d : G) * t :=
          Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2 t (by simp)
        rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      have h1 : (((ctD d)⁻¹ * d : ↥D) : G) = 1 := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hctD_apply, hdt, inv_mul_cancel]
      rw [h1]
      exact (Work.ThmF.W H t).one_mem
  -- F(P) meets the image of V trivially
  have hA_inter_V : ∀ d : ↥D,
      QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D) d ∈ Work.Fitting.fitting P →
      (d : G) ∈ Submission.Blueprint.centD H t →
      QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D) d = 1 := by
    intro d hd hV
    by_contra hne
    obtain ⟨u, hu, hVu⟩ := hP2a
    have huQ : u ∈ Work.ThmF.Q0sub H := Work.ThmF.Q0_le_Q0sub H (Or.inl hu)
    have hu1 : u ≠ 1 := by
      intro h1
      have h2 := hu.2
      rw [h1, orderOf_one] at h2
      omega
    have hVinf : (d : G) ∈ Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer {u} := hVu ▸ hV
    have hc : u * (d : G) = (d : G) * u :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hVinf).2) u (by simp)
    have hfix : ρ (QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D) d) ⟨u, huQ⟩ = ⟨u, huQ⟩ := by
      apply Subtype.ext
      rw [hρ_mk, hψ_apply, ← hc, mul_assoc, mul_inv_cancel, mul_one]
    have h1 := hFfpf _ hd hne ⟨u, huQ⟩ hfix
    exact hu1 (congrArg Subtype.val h1)
  -- App I on A = F(P): tau inverts A
  have hFchar : (Work.Fitting.fitting P).Characteristic := Work.Fitting.fitting_characteristic_inst P
  haveI hFn : (Work.Fitting.fitting P).Normal := inferInstance
  have hFτ : ∀ x ∈ Work.Fitting.fitting P, τ x ∈ Work.Fitting.fitting P := by
    intro x hx
    have hmap := (Subgroup.characteristic_iff_map_eq.mp hFchar) τ
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  let τA : ↥(Work.Fitting.fitting P) →* ↥(Work.Fitting.fitting P) :=
    { toFun := fun x => ⟨τ x, hFτ x x.2⟩
      map_one' := Subtype.ext (map_one τ)
      map_mul' := fun a b => Subtype.ext (map_mul τ (a : P) (b : P)) }
  have hτA2 : ∀ x, τA (τA x) = x := by
    intro x
    apply Subtype.ext
    exact hτ2 (x : P)
  have hτA_fpf : ∀ x : ↥(Work.Fitting.fitting P), τA x = x → x = 1 := by
    intro x hx
    obtain ⟨d, hd⟩ := QuotientGroup.mk'_surjective ((Work.ThmF.W H t).subgroupOf D) (x : P)
    have hxτ : τ (x : P) = (x : P) :=
      congrArg (fun y : ↥(Work.Fitting.fitting P) => (y : P)) hx
    have hdτ : τ (QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D) d)
        = QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D) d := by
      rw [hd]
      exact hxτ
    have hdV : (d : G) ∈ Submission.Blueprint.centD H t := (hCτ d).mp hdτ
    have hmem : QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D) d ∈ Work.Fitting.fitting P := by
      rw [hd]
      exact x.2
    have h1 := hA_inter_V d hmem hdV
    apply Subtype.ext
    show (x : P) = ((1 : ↥(Work.Fitting.fitting P)) : P)
    rw [← hd]
    exact h1
  have hτA_inv : ∀ x : ↥(Work.Fitting.fitting P), τA x = x⁻¹ :=
    Work.ZassenhausPSL2.ZData.eq_inv_of_fpf_order_two τA hτA2 hτA_fpf
  have hF_inv : ∀ x ∈ Work.Fitting.fitting P, τ x = x⁻¹ := by
    intro x hx
    have h := congrArg (fun y : ↥(Work.Fitting.fitting P) => (y : P)) (hτA_inv ⟨x, hx⟩)
    show τ x = x⁻¹
    exact h

  -- J = {x : tau x = x^-1} is a subgroup and equals F(P)
  obtain ⟨J, hJset, hJn, hJcomm, hAJ⟩ :=
    metabelianInverted τ hτ2 hP_odd (Work.Fitting.fitting P) hFn hFcomm hF_inv
  haveI hJcommI : IsMulCommutative ↥J :=
    isMulCommutative_iff.mpr (fun a b => Subtype.ext (hJcomm a a.2 b b.2))
  haveI hJnil : Group.IsNilpotent ↥J := CommGroup.isNilpotent
  have hJ_le_F : J ≤ Work.Fitting.fitting P := Work.Fitting.le_fitting hJn inferInstance
  have hJ_eq : J = Work.Fitting.fitting P := le_antisymm hJ_le_F hAJ
  have hkD : ∀ k : ↥(Work.ThmF.Kset H t), (k : G) ∈ D := by
    intro k
    rw [hD]
    exact Work.ThmF.Kset_subset H t k.2
  -- the image of K in P lies in the Fitting subgroup
  have hKbar : ∀ k : ↥(Work.ThmF.Kset H t),
      QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D)
        ⟨(k : G), hkD k⟩ ∈ Work.Fitting.fitting P := by
    intro k
    have hkinJ : (QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D)
        ⟨(k : G), hkD k⟩ : P) ∈ (J : Set P) := by
      rw [hJset]
      show τ (QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D) (⟨(k : G), hkD k⟩ : ↥D))
        = (QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D) (⟨(k : G), hkD k⟩ : ↥D))⁻¹
      have hkK : t * (k : G) * t⁻¹ = (k : G)⁻¹ := (Work.ThmF.mem_Kset_iff.mp k.2).2
      rw [hτ_mk, ← map_inv]
      congr 1
      apply Subtype.ext
      rw [hctD_apply, Subgroup.coe_inv]
      exact hkK
    rw [← hJ_eq]
    exact hkinJ
  -- the map K -> P given by k |-> k W is injective
  have hKset_inj : Function.Injective
      (fun k : ↥(Work.ThmF.Kset H t) => QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D)
        ⟨(k : G), hkD k⟩) := by
    intro k k' hkk
    have h1 : (⟨(k : G), hkD k⟩ : ↥D)⁻¹
        * ⟨(k' : G), hkD k'⟩
        ∈ (Work.ThmF.W H t).subgroupOf D := by
      have h2 : (↑(⟨(k : G), hkD k⟩ : ↥D) : P)
          = ↑(⟨(k' : G), hkD k'⟩ : ↥D) := hkk
      rwa [QuotientGroup.eq] at h2
    have h3 : (k : G)⁻¹ * (k' : G) ∈ Work.ThmF.W H t := by
      have h4 := Subgroup.mem_subgroupOf.mp h1
      simpa using h4
    obtain ⟨u, hu, hVu⟩ := hP2a
    have hWu : Work.ThmF.W H t
        ≤ Subgroup.centralizer (Submission.Blueprint.involutions (H : Set G)) := by
      rw [hW_eq]; exact inf_le_right
    have hcm : u * ((k : G)⁻¹ * (k' : G)) = ((k : G)⁻¹ * (k' : G)) * u :=
      Subgroup.mem_centralizer_iff.mp (hWu h3) u hu
    have hconj : ((k : G)⁻¹ * (k' : G)) * u * ((k : G)⁻¹ * (k' : G))⁻¹ = u := by
      rw [← hcm]; group
    have hku : (k : G) * u * (k : G)⁻¹ = (k' : G) * u * (k' : G)⁻¹ := by
      have key := congrArg (fun z : G => (k : G) * z * (k : G)⁻¹) hconj
      have key2 : (k : G) * ((k : G)⁻¹ * (k' : G) * u * ((k : G)⁻¹ * (k' : G))⁻¹) * (k : G)⁻¹
          = (k' : G) * u * (k' : G)⁻¹ := by group
      rw [key2] at key
      exact key.symm
    exact Subtype.ext (Work.ThmF.Bender.Kset_conj_injective h.stronglyEmbedded h.invol h.not_mem
      hu.1 hu.2 k.2 k'.2 hku)
  -- |F(P)| <= |K|
  have hcard_F_le : Nat.card ↥(Work.Fitting.fitting P) ≤ (Work.ThmF.Kset H t).ncard := by
    obtain ⟨u, hu, hVu⟩ := hP2a
    have huQ : u ∈ Work.ThmF.Q0sub H := Work.ThmF.Q0_le_Q0sub H (Or.inl hu)
    have hu1 : u ≠ 1 := by
      intro h1
      have h2 := hu.2
      rw [h1, orderOf_one] at h2
      omega
    have hmap : ∀ x : ↥(Work.Fitting.fitting P),
        Subtype.val (ρ (x : P) ⟨u, huQ⟩) ∈ Submission.Blueprint.involutions (H : Set G) := by
      intro x
      have hρx : Subtype.val (ρ (x : P) ⟨u, huQ⟩) ≠ 1 := by
        intro h1
        have h2 : (ρ (x : P) ⟨u, huQ⟩) = (ρ (x : P) (1 : ↥(Work.ThmF.Q0sub H))) := by
          rw [show (ρ (x : P) ⟨u, huQ⟩) = 1 from Subtype.ext h1, map_one]
        have h3 := (ρ (x : P)).injective h2
        exact hu1 (congrArg Subtype.val h3)
      exact hQ0inv (Subtype.val (ρ (x : P) ⟨u, huQ⟩)) (ρ (x : P) ⟨u, huQ⟩).2 hρx
    let f : ↥(Work.Fitting.fitting P) → ↥(Submission.Blueprint.involutions (H : Set G)) :=
      fun x => ⟨Subtype.val (ρ (x : P) ⟨u, huQ⟩), hmap x⟩
    have hf_inj : Function.Injective f := by
      intro x y hxy
      have h2 : (ρ (x : P) ⟨u, huQ⟩) = ρ (y : P) ⟨u, huQ⟩ := by
        have h2G : Subtype.val (f x) = Subtype.val (f y) := congrArg Subtype.val hxy
        apply Subtype.ext
        exact h2G
      have h3 : (ρ ((x : P)⁻¹ * (y : P))) ⟨u, huQ⟩ = ⟨u, huQ⟩ := by
        rw [map_mul, map_inv]
        show ((ρ (x : P))⁻¹ * ρ (y : P)) ⟨u, huQ⟩ = ⟨u, huQ⟩
        rw [MulAut.mul_apply]
        show (ρ (x : P)).symm ((ρ (y : P)) ⟨u, huQ⟩) = ⟨u, huQ⟩
        rw [← h2, MulEquiv.symm_apply_apply]
      have hmem : (x : P)⁻¹ * (y : P) ∈ Work.Fitting.fitting P :=
        (Work.Fitting.fitting P).mul_mem ((Work.Fitting.fitting P).inv_mem x.2) y.2
      by_cases h1 : (x : P)⁻¹ * (y : P) = 1
      · exact Subtype.ext (inv_mul_eq_one.mp h1)
      · exfalso
        have h4 := hFfpf _ hmem h1 ⟨u, huQ⟩ h3
        exact hu1 (congrArg Subtype.val h4)
    have hcard := Nat.card_le_card_of_injective f hf_inj
    have hcard2 : Nat.card ↥(Submission.Blueprint.involutions (H : Set G))
        = (Work.ThmF.Kset H t).ncard := by
      rw [Nat.card_coe_set_eq]
      exact (Work.ThmF.Bender.cardKsetEqInv h.stronglyEmbedded h.invol h.not_mem).symm
    rwa [hcard2] at hcard
  -- |K| <= |F(P)|
  have hcard_K_le : (Work.ThmF.Kset H t).ncard ≤ Nat.card ↥(Work.Fitting.fitting P) := by
    have hcard := Nat.card_le_card_of_injective
      (fun k : ↥(Work.ThmF.Kset H t) => (⟨QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D)
        ⟨(k : G), hkD k⟩, hKbar k⟩ : ↥(Work.Fitting.fitting P)))
      (fun a b hab => hKset_inj (Subtype.ext_iff.mp hab))
    rwa [Nat.card_coe_set_eq] at hcard
  have hcard_eq : (Work.ThmF.Kset H t).ncard = Nat.card ↥(Work.Fitting.fitting P) :=
    le_antisymm hcard_K_le hcard_F_le
  -- the image of K is all of F(P)
  have hKbar_eq : (fun k : ↥(Work.ThmF.Kset H t) => QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D)
        ⟨(k : G), hkD k⟩) ''
      (Set.univ : Set ↥(Work.ThmF.Kset H t))
      = (Work.Fitting.fitting P : Set P) := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
    · rintro x ⟨k, -, rfl⟩
      exact hKbar k
    · rw [Set.InjOn.ncard_image]
      · rw [Set.ncard_univ]
        exact hcard_eq.symm.trans_le (Nat.card_coe_set_eq (Work.ThmF.Kset H t)).ge
      · intro a _ b _ hab
        exact hKset_inj hab
  -- a generator of F(P), lifted to K
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(Work.Fitting.fitting P))
  have hgK : (g : P) ∈ (Work.Fitting.fitting P : Set P) := g.2
  rw [← hKbar_eq] at hgK
  obtain ⟨k0, -, hk0⟩ := hgK
  set k0g : G := (k0 : G) with hk0g
  have horder_k0 : orderOf g ≤ orderOf k0g := by
    have h1 : orderOf (QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D)
        (⟨k0g, hkD k0⟩ : ↥D) : P) ∣ orderOf k0g := by
      have h2 := orderOf_map_dvd (QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D))
        (⟨k0g, hkD k0⟩ : ↥D)
      rw [Subgroup.orderOf_mk] at h2
      exact h2
    have hk0' : QuotientGroup.mk' ((Work.ThmF.W H t).subgroupOf D) (⟨k0g, hkD k0⟩ : ↥D)
        = (g : P) := hk0
    rw [hk0'] at h1
    have h4 : orderOf g = orderOf (g : P) := Subgroup.orderOf_mk (g : P) g.2
    rw [h4]
    exact Nat.le_of_dvd (orderOf_pos _) h1
  have hgen_card : orderOf g = (Work.ThmF.Kset H t).ncard := by
    have h2 : Subgroup.zpowers g = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro y
      exact hg y
    have h3 : orderOf g = Nat.card ↥(⊤ : Subgroup ↥(Work.Fitting.fitting P)) := by
      rw [← Nat.card_zpowers g, h2]
    rw [h3, Subgroup.card_top]
    exact hcard_eq.symm
  have hzpow_mem : ∀ {x : G}, x ∈ Work.ThmF.Kset H t → ∀ n : ℤ, x ^ n ∈ Work.ThmF.Kset H t := by
    intro x hx n
    obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg n
    · rw [hm, zpow_natCast]; exact Work.ThmF.pow_mem_Kset hx m
    · rw [hm, zpow_neg, zpow_natCast]
      have hinv : x⁻¹ ∈ Work.ThmF.Kset H t := by
        obtain ⟨hxD, hxinv⟩ := Work.ThmF.mem_Kset_iff.mp hx
        refine Work.ThmF.mem_Kset_iff.mpr ⟨(Submission.Blueprint.twoPoint H t).inv_mem hxD, ?_⟩
        rw [show t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ by group, hxinv]
      simpa [inv_pow] using Work.ThmF.pow_mem_Kset hinv m
  have hzpow_le : (Subgroup.zpowers k0g : Set G) ⊆ Work.ThmF.Kset H t := by
    intro x hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hn]
    exact hzpow_mem k0.2 n
  let f2 : ↥(Subgroup.zpowers k0g) → ↥(Work.ThmF.Kset H t) :=
    fun x => ⟨Subtype.val x, hzpow_le x.2⟩
  have hf2_inj : Function.Injective f2 := by
    intro a b hab
    have h : Subtype.val (f2 a) = Subtype.val (f2 b) := congrArg Subtype.val hab
    apply Subtype.ext
    exact h
  have hzpow_card : Nat.card ↥(Subgroup.zpowers k0g) = (Work.ThmF.Kset H t).ncard := by
    have hle : orderOf k0g ≤ (Work.ThmF.Kset H t).ncard := by
      rw [← Nat.card_zpowers k0g]
      exact (Nat.card_le_card_of_injective f2 hf2_inj).trans
        (Nat.card_coe_set_eq (Work.ThmF.Kset H t)).le
    have hge : (Work.ThmF.Kset H t).ncard ≤ orderOf k0g := hgen_card ▸ horder_k0
    rw [Nat.card_zpowers]
    exact le_antisymm hle hge
  have hcard_le : (Work.ThmF.Kset H t).ncard ≤ (Subgroup.zpowers k0g : Set G).ncard :=
    ((Nat.card_coe_set_eq (Work.ThmF.Kset H t)).symm.trans
      (hzpow_card.symm.trans (Nat.card_coe_set_eq (Subgroup.zpowers k0g : Set G)))).le
  have hzpow_eq : (Subgroup.zpowers k0g : Set G) = Work.ThmF.Kset H t :=
    Set.eq_of_subset_of_ncard_le hzpow_le hcard_le (Set.toFinite _)
  -- conclude
  have hKsub_eq : Work.ThmF.Ksub H t = Subgroup.zpowers k0g := by
    show Subgroup.closure (Work.ThmF.Kset H t) = Subgroup.zpowers k0g
    rw [← hzpow_eq, Subgroup.closure_eq]
  have hKset_eq : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t := by
    have h1 : (Work.ThmF.Ksub H t : Set G) = (Subgroup.zpowers k0g : Set G) := by
      rw [hKsub_eq]
    rw [h1, hzpow_eq]
  refine ⟨?_, hKset_eq, ?_⟩
  · rw [hKsub_eq]; exact Subgroup.isCyclic_zpowers k0g
  · exact Work.ThmF.ChV12.KsubSubgroupOfNormal h hKset_eq

end Work.ThmF.ChV12
