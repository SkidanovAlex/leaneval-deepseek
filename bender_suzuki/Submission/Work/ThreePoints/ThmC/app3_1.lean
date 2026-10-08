/-
# `Work.ThreePoints.ThmC.app3_1` — Peterfalvi I, Appendix III (1) (p. 206)

The two-point stabiliser `H ⊓ H^t` of a `2`-rank-`1` group with a maximal proper Bender subgroup
`H` fixes the fixed point of the involution `t`.

The proof is the paper's: from Brauer–Suzuki (`hBrSz`) and Feit–Thompson (`hFT`) one gets a normal
subgroup `Q ⊴ F` with `Q ⊄ H`, `Q ⊔ H = ⊤` (maximality of `H`), `⁅Q,Q⁆ ≤ H` and `|Q|` odd.  With
`N = Q ⊓ H`, the quotient `V = Q/N` is an abelian group of odd order in bijection with `A`
(`q ↦ q • a`), `t = q₀ h₀` with `q₀ ∈ Q`, `h₀ ∈ H`, and the fixed points of `t` correspond to the
solutions of `q₀ · (h₀ x h₀⁻¹) = x` in `V`.  Uniqueness of the fixed point of `t` forces `h₀` to
act by inversion on `V`, so that `q₀ = x₀²` where `b = x₀ • a`; then the `H`-stabilisers of
`t • a = q₀ • a` and of `b = x₀ • a` are both the set of `h ∈ H` with `h q₀ h⁻¹ ≡ q₀ (mod N)`.
-/
import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.ThreePoints.ThmC.exists_normal_commutator_le
import Submission.Work.ThreePoints.centD_eq_centralizer_of_involution
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore
import Submission.Work.BrauerSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ThreePoints.ThmC

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {F A : Type} [Group F] [MulAction F A]

/-! ## 1. Elementary lemmas -/

/-- Conjugation identity for the action: `g • (y • c) = (g * y * g⁻¹) • (g • c)`. -/
theorem app3_1_smul_conj (g y : F) (c : A) :
    g • (y • c) = (g * y * g⁻¹) • (g • c) := by
  calc g • (y • c) = (g * y) • c := (mul_smul g y c).symm
    _ = ((g * y * g⁻¹) * g) • c := by congr 1; group
    _ = (g * y * g⁻¹) • (g • c) := mul_smul _ _ _

/-- In a finite group of odd order the squaring map is injective. -/
theorem app3_1_sq_eq_of_odd_card {G : Type} [Group G] [Finite G] (hodd : Odd (Nat.card G))
    {x y : G} (h : x ^ 2 = y ^ 2) : x = y := by
  haveI : Fintype G := Fintype.ofFinite G
  have hdvd : 2 ∣ Nat.card G + 1 := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k + 1, by omega⟩
  have hx : x ^ (Nat.card G + 1) = x := by
    rw [Nat.card_eq_fintype_card, pow_succ, pow_card_eq_one, one_mul]
  have hy : y ^ (Nat.card G + 1) = y := by
    rw [Nat.card_eq_fintype_card, pow_succ, pow_card_eq_one, one_mul]
  have hx2 : (x ^ 2) ^ ((Nat.card G + 1) / 2) = x := by
    rw [← pow_mul, Nat.mul_div_cancel' hdvd, hx]
  have hy2 : (y ^ 2) ^ ((Nat.card G + 1) / 2) = y := by
    rw [← pow_mul, Nat.mul_div_cancel' hdvd, hy]
  rw [← hx2, ← hy2, h]

/-- Conjugation by an element of the ambient group, as a self-map of `Q`. -/
def app3_1_conjQ (Q : Subgroup F) (hQ : Q.Normal) (h : F) (x : ↥Q) : ↥Q :=
  ⟨h * (x : F) * h⁻¹, hQ.conj_mem (x : F) x.2 h⟩

@[simp] theorem app3_1_conjQ_coe (Q : Subgroup F) (hQ : Q.Normal) (h : F) (x : ↥Q) :
    ((app3_1_conjQ Q hQ h x : ↥Q) : F) = h * (x : F) * h⁻¹ := rfl

theorem app3_1_conjQ_mul (Q : Subgroup F) (hQ : Q.Normal) (h : F) (x y : ↥Q) :
    app3_1_conjQ Q hQ h (x * y) = app3_1_conjQ Q hQ h x * app3_1_conjQ Q hQ h y := by
  ext
  show h * ((x : F) * (y : F)) * h⁻¹ = (h * (x : F) * h⁻¹) * (h * (y : F) * h⁻¹)
  group

theorem app3_1_conjQ_inv (Q : Subgroup F) (hQ : Q.Normal) (h : F) (x : ↥Q) :
    app3_1_conjQ Q hQ h x⁻¹ = (app3_1_conjQ Q hQ h x)⁻¹ := by
  ext
  show h * ((x : F))⁻¹ * h⁻¹ = (h * (x : F) * h⁻¹)⁻¹
  group

@[simp] theorem app3_1_conjQ_one (Q : Subgroup F) (hQ : Q.Normal) (h : F) :
    app3_1_conjQ Q hQ h 1 = 1 := by
  ext
  show h * (1 : F) * h⁻¹ = 1
  group

/-! ## 2. The core of Appendix III (1) -/

/-- **Core of Peterfalvi I Appendix III (1).**  Let `F` act transitively on `A`, let `Q ⊴ F` with
`Q ⊔ H = ⊤`, `H` the stabiliser of `a ∈ A`, `⁅Q,Q⁆ ≤ H` and `|Q|` odd.  If `t ∈ F` is an
involution (`t * t = 1`) whose unique fixed point is `b`, then `H ⊓ H^t = H ⊓ Stab b`.

Writing `N = Q ⊓ H` and `V = Q/N` (an abelian group of odd order, in bijection with `A` via
`q ↦ q • a`), the element `t` decomposes as `t = q₀ h₀` with `q₀ ∈ Q`, `h₀ ∈ H`, and the fixed
points of `t` correspond to the solutions of `q₀ · (h₀ x h₀⁻¹) = x` in `V`.  Uniqueness of the
fixed point forces `h₀` to act by inversion on `V`, so that `q₀ = x²` where `b = x • a`; then both
the `H`-stabiliser of `t • a = q₀ • a` and that of `b = x • a` are the set of `h ∈ H` with
`h q₀ h⁻¹ ≡ q₀ (mod N)`. -/
theorem app3_1_core [Finite F] {a b : A} {H Q : Subgroup F}
    (htrans : MulAction.IsPretransitive F A) (hHa : H = MulAction.stabilizer F a)
    (hQnorm : Q.Normal) (hQH : Q ⊔ H = ⊤) (hder : ⁅Q,Q⁆ ≤ H) (hQodd : Odd (Nat.card ↥Q))
    {t : F} (ht2 : t ^ 2 = 1) (hb : t • b = b) (hbuniq : ∀ c : A, t • c = c → c = b) :
    H ⊓ conj t H = H ⊓ MulAction.stabilizer F b := by
  classical
  haveI hQnormI : Q.Normal := hQnorm
  haveI htransI : MulAction.IsPretransitive F A := htrans
  -- 0. `Q` is transitive on `A`
  have hQtrans : ∀ c : A, ∃ q : ↥Q, (q : F) • a = c := by
    intro c
    obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := F) a c
    obtain ⟨q, hqQ, h, hhH, hqht⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := Q) (t := H) (x := g)).mp (by rw [hQH]; trivial)
    refine ⟨⟨q, hqQ⟩, ?_⟩
    have hha : h • a = a := MulAction.mem_stabilizer_iff.mp (hHa ▸ hhH)
    rw [← hg, ← hqht, mul_smul, hha]
  -- 1. `N = Q ⊓ H` as a subgroup of `Q`, normal in `Q` because `⁅Q,Q⁆ ≤ H`
  set NQ : Subgroup ↥Q := H.subgroupOf Q with hNQdef
  have hNQnorm : NQ.Normal := by
    refine Subgroup.Normal.mk fun n hn q => ?_
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hcomm : ((q : F) * (n : F) * (q : F)⁻¹ * (n : F)⁻¹) ∈ H :=
      (Subgroup.commutator_le.mp hder) (q : F) q.2 (n : F) n.2
    have heq : ((q * n * q⁻¹ : ↥Q) : F) =
        (q : F) * (n : F) * (q : F)⁻¹ * (n : F)⁻¹ * (n : F) := by
      show (q : F) * (n : F) * (q : F)⁻¹ = (q : F) * (n : F) * (q : F)⁻¹ * (n : F)⁻¹ * (n : F)
      group
    rw [heq]
    exact H.mul_mem hcomm hn
  haveI hNQnormI : NQ.Normal := hNQnorm
  haveI hVcomm : IsMulCommutative ((↥Q) ⧸ NQ) := by
    rw [Subgroup.Normal.quotient_commutative_iff_commutator_le, commutator_def,
      Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_subgroupOf]
    exact (Subgroup.commutator_le.mp hder) x x.2 y y.2
  have hVodd : Odd (Nat.card ((↥Q) ⧸ NQ)) :=
    Odd.of_dvd_nat hQodd (Subgroup.card_quotient_dvd_card NQ)
  -- dictionary between the quotient `V` and `A`
  have mk_eq_iff : ∀ q q' : ↥Q, QuotientGroup.mk' NQ q = QuotientGroup.mk' NQ q' ↔
      q⁻¹ * q' ∈ NQ := by
    intro q q'
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  -- 2. `t = q₀ * h₀`
  obtain ⟨q0, hq0Q, h0, hh0H, ht_eq⟩ : ∃ q0 ∈ Q, ∃ h0 ∈ H, q0 * h0 = t :=
    (Subgroup.mem_sup_of_normal_left (s := Q) (t := H) (x := t)).mp (by rw [hQH]; trivial)
  have h0a : h0 • a = a := MulAction.mem_stabilizer_iff.mp (hHa ▸ hh0H)
  have ht_a : t • a = ((⟨q0, hq0Q⟩ : ↥Q) : F) • a := by
    have h1 : t • a = q0 • a := by rw [← ht_eq, mul_smul, h0a]
    exact h1
  -- 3. the dictionary `q • a = q' • a ↔ q = q' in V`
  have key_mem : ∀ q q' : ↥Q, (q : F) • a = (q' : F) • a ↔
      QuotientGroup.mk' NQ q = QuotientGroup.mk' NQ q' := by
    intro q q'
    rw [mk_eq_iff]
    constructor
    · intro h
      rw [Subgroup.mem_subgroupOf]
      have h3 : ((q⁻¹ * q' : ↥Q) : F) • a = a := by
        have h4 := congrArg (fun z => (q : F)⁻¹ • z) h
        rw [← mul_smul, inv_mul_cancel, one_smul] at h4
        calc ((q⁻¹ * q' : ↥Q) : F) • a = ((q : F)⁻¹ * (q' : F)) • a := by
              rw [show ((q⁻¹ * q' : ↥Q) : F) = (q : F)⁻¹ * (q' : F) from rfl]
          _ = (q : F)⁻¹ • ((q' : F) • a) := mul_smul _ _ _
          _ = a := h4.symm
      exact hHa.symm ▸ MulAction.mem_stabilizer_iff.mpr h3
    · intro h
      have ha : ((q⁻¹ * q' : ↥Q) : F) • a = a :=
        MulAction.mem_stabilizer_iff.mp (hHa ▸ Subgroup.mem_subgroupOf.mp h)
      calc (q : F) • a = (q : F) • (((q⁻¹ * q' : ↥Q) : F) • a) := by rw [ha]
        _ = ((q * (q⁻¹ * q') : ↥Q) : F) • a := by
              rw [show ((q * (q⁻¹ * q') : ↥Q) : F) = (q : F) * ((q⁻¹ * q' : ↥Q) : F) from rfl,
                mul_smul]
        _ = (q' : F) • a := by
              rw [show ((q * (q⁻¹ * q') : ↥Q) : F) = (q' : F) from by push_cast; group]
  -- 4. conjugation of `Q` by elements of `H`
  have cjH_mem : ∀ (h : F) (hh : h ∈ H) (x : ↥Q),
      x ∈ NQ → app3_1_conjQ Q hQnorm h x ∈ NQ := by
    intro h hh x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [app3_1_conjQ_coe]
    exact H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)
  have cjH_resp : ∀ (h : F) (hh : h ∈ H) (x y : ↥Q),
      QuotientGroup.mk' NQ x = QuotientGroup.mk' NQ y →
      QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h x) =
        QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h y) := by
    intro h hh x y hxy
    rw [mk_eq_iff] at hxy ⊢
    rw [← app3_1_conjQ_inv Q hQnorm h x, ← app3_1_conjQ_mul Q hQnorm h x⁻¹ y]
    exact cjH_mem h hh (x⁻¹ * y) hxy
  -- conjugating a normal element
  have hNQ_conj : ∀ (u z : ↥Q), u ∈ NQ → QuotientGroup.mk' NQ (u * z * u⁻¹) =
      QuotientGroup.mk' NQ z := by
    intro u z hu
    rw [mk_eq_iff]
    have h1 : (u * z * u⁻¹)⁻¹ * z = u * (z⁻¹ * u⁻¹ * z) := by
      ext
      show ((u : F) * (z : F) * (u : F)⁻¹)⁻¹ * (z : F) =
        (u : F) * ((z : F)⁻¹ * (u : F)⁻¹ * (z : F))
      group
    rw [h1]
    exact NQ.mul_mem hu (hNQnorm.conj_mem' u⁻¹ (NQ.inv_mem hu) z)
  -- 5. `h₀` acts as an involution on `V` (from `t * t = 1`)
  have hh0sq : ∀ z : ↥Q,
      QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h0 (app3_1_conjQ Q hQnorm h0 z)) =
        QuotientGroup.mk' NQ z := by
    have hsq : q0 * (h0 * q0 * h0⁻¹) * (h0 * h0) = 1 := by
      have h := ht2
      rw [← ht_eq, pow_two] at h
      calc q0 * (h0 * q0 * h0⁻¹) * (h0 * h0) = (q0 * h0) * (q0 * h0) := by group
        _ = 1 := h
    have hsqQ : h0 * h0 ∈ Q := by
      have h : h0 * h0 = (q0 * (h0 * q0 * h0⁻¹))⁻¹ := by
        rw [eq_inv_of_mul_eq_one_right hsq]
      rw [h]
      exact Q.inv_mem (Q.mul_mem hq0Q (hQnorm.conj_mem q0 hq0Q h0))
    have huN : (⟨h0 * h0, hsqQ⟩ : ↥Q) ∈ NQ := by
      rw [Subgroup.mem_subgroupOf]
      exact H.mul_mem hh0H hh0H
    intro z
    have hconjz : app3_1_conjQ Q hQnorm h0 (app3_1_conjQ Q hQnorm h0 z) =
        ⟨h0 * h0, hsqQ⟩ * z * ⟨h0 * h0, hsqQ⟩⁻¹ := by
      ext
      show h0 * (h0 * (z : F) * h0⁻¹) * h0⁻¹ = (h0 * h0) * (z : F) * (h0 * h0)⁻¹
      group
    rw [hconjz]
    exact hNQ_conj ⟨h0 * h0, hsqQ⟩ z huN
  -- 6. the dictionary between fixed points of `t` and solutions in `V`
  have hfix_iff : ∀ x : ↥Q, t • ((x : F) • a) = ((x : F) • a) ↔
      QuotientGroup.mk' NQ ⟨q0, hq0Q⟩ * QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h0 x) =
        QuotientGroup.mk' NQ x := by
    intro x
    have hinner : h0 • ((x : F) • a) = ((app3_1_conjQ Q hQnorm h0 x : ↥Q) : F) • a := by
      rw [app3_1_smul_conj, h0a]
      exact congrArg (fun z : F => z • a) (app3_1_conjQ_coe Q hQnorm h0 x).symm
    have haux : t • ((x : F) • a) = ((⟨q0, hq0Q⟩ * app3_1_conjQ Q hQnorm h0 x : ↥Q) : F) • a := by
      calc t • ((x : F) • a) = (q0 * h0) • ((x : F) • a) := by rw [← ht_eq]
        _ = q0 • (h0 • ((x : F) • a)) := by rw [mul_smul]
        _ = q0 • (((app3_1_conjQ Q hQnorm h0 x : ↥Q) : F) • a) := by rw [hinner]
        _ = ((⟨q0, hq0Q⟩ * app3_1_conjQ Q hQnorm h0 x : ↥Q) : F) • a := by
              rw [show ((⟨q0, hq0Q⟩ * app3_1_conjQ Q hQnorm h0 x : ↥Q) : F)
                = q0 * ((app3_1_conjQ Q hQnorm h0 x : ↥Q) : F) from rfl, mul_smul]
    rw [haux, key_mem, map_mul]
  -- 7. `b = x₀ • a`
  obtain ⟨x0, hx0⟩ := hQtrans b
  have hW : QuotientGroup.mk' NQ ⟨q0, hq0Q⟩ * QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h0 x0) =
      QuotientGroup.mk' NQ x0 := (hfix_iff x0).mp (by rw [hx0]; exact hb)
  -- 8. the solutions are exactly `x₀`
  have hsol : ∀ x : ↥Q,
      (QuotientGroup.mk' NQ ⟨q0, hq0Q⟩ * QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h0 x)
        = QuotientGroup.mk' NQ x) ↔ QuotientGroup.mk' NQ x = QuotientGroup.mk' NQ x0 := by
    intro x
    rw [← hfix_iff x]
    constructor
    · intro h
      exact (key_mem x x0).mp (by rw [hbuniq ((x : F) • a) h, hx0])
    · intro h
      rw [show (x : F) • a = b from by rw [(key_mem x x0).mpr h, hx0]]
      exact hb
  -- 9. the conjugation has no non-trivial fixed point in `V`
  have hK1 : ∀ z : ↥Q, QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h0 z) = QuotientGroup.mk' NQ z →
      QuotientGroup.mk' NQ z = 1 := by
    intro z hz
    have h1 : QuotientGroup.mk' NQ ⟨q0, hq0Q⟩ *
        QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h0 (x0 * z)) =
        QuotientGroup.mk' NQ (x0 * z) := by
      calc QuotientGroup.mk' NQ ⟨q0, hq0Q⟩ *
            QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h0 (x0 * z))
          = QuotientGroup.mk' NQ ⟨q0, hq0Q⟩ *
              (QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h0 x0) *
                QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h0 z)) := by
                simp only [app3_1_conjQ_mul Q hQnorm, map_mul]
        _ = (QuotientGroup.mk' NQ ⟨q0, hq0Q⟩ *
              QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h0 x0)) *
              QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h0 z) := by rw [mul_assoc]
        _ = QuotientGroup.mk' NQ x0 * QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h0 z) := by
              rw [hW]
        _ = QuotientGroup.mk' NQ x0 * QuotientGroup.mk' NQ z := by rw [hz]
        _ = QuotientGroup.mk' NQ (x0 * z) := (map_mul _ _ _).symm
    have h2 := (hsol (x0 * z)).mp h1
    rw [map_mul] at h2
    exact mul_left_cancel (by rw [h2, mul_one])
  -- 10. `h₀` acts on `V` by inversion
  have hρinv : ∀ z : ↥Q, QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h0 z) =
      (QuotientGroup.mk' NQ z)⁻¹ := by
    intro z
    have hfixz : QuotientGroup.mk' NQ
        (app3_1_conjQ Q hQnorm h0 (z * app3_1_conjQ Q hQnorm h0 z)) =
        QuotientGroup.mk' NQ (z * app3_1_conjQ Q hQnorm h0 z) := by
      calc QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h0 (z * app3_1_conjQ Q hQnorm h0 z))
          = QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h0 z *
              app3_1_conjQ Q hQnorm h0 (app3_1_conjQ Q hQnorm h0 z)) := by
            rw [app3_1_conjQ_mul Q hQnorm]
        _ = QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h0 z) *
              QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h0 (app3_1_conjQ Q hQnorm h0 z)) :=
              map_mul _ _ _
        _ = QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h0 z) * QuotientGroup.mk' NQ z := by
              rw [hh0sq]
        _ = QuotientGroup.mk' NQ z * QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h0 z) :=
              (IsMulCommutative.is_comm (M := (↥Q) ⧸ NQ)).comm _ _
        _ = QuotientGroup.mk' NQ (z * app3_1_conjQ Q hQnorm h0 z) := (map_mul _ _ _).symm
    have h1 := hK1 (z * app3_1_conjQ Q hQnorm h0 z) hfixz
    rw [map_mul] at h1
    exact mul_left_cancel (by rw [h1, mul_inv_cancel])
  -- 11. `q₀` is a square
  have hv_eq : QuotientGroup.mk' NQ x0 * QuotientGroup.mk' NQ x0 =
      QuotientGroup.mk' NQ ⟨q0, hq0Q⟩ := by
    have h := hW
    rw [hρinv x0] at h
    calc QuotientGroup.mk' NQ x0 * QuotientGroup.mk' NQ x0
        = (QuotientGroup.mk' NQ ⟨q0, hq0Q⟩ * (QuotientGroup.mk' NQ x0)⁻¹) *
            QuotientGroup.mk' NQ x0 := by rw [h]
      _ = QuotientGroup.mk' NQ ⟨q0, hq0Q⟩ := by group
  -- 12. the two conditions on `h ∈ H` coincide
  have hconj : conj t H = MulAction.stabilizer F (t • a) := by
    rw [hHa]
    exact (MulAction.stabilizer_smul_eq_stabilizer_map_conj t a).symm
  have hchar1 : ∀ h : F, h ∈ H → (h ∈ conj t H ↔
      QuotientGroup.mk' NQ ⟨h * q0 * h⁻¹, hQnorm.conj_mem q0 hq0Q h⟩ =
        QuotientGroup.mk' NQ ⟨q0, hq0Q⟩) := by
    intro h hhH
    have hha : h • a = a := MulAction.mem_stabilizer_iff.mp (hHa ▸ hhH)
    have haux : h • (((⟨q0, hq0Q⟩ : ↥Q) : F) • a) =
        ((⟨h * q0 * h⁻¹, hQnorm.conj_mem q0 hq0Q h⟩ : ↥Q) : F) • a := by
      simp only [app3_1_smul_conj, hha]
    rw [hconj, MulAction.mem_stabilizer_iff, ht_a, haux, key_mem]
  have hchar2 : ∀ h : F, h ∈ H → (h ∈ MulAction.stabilizer F b ↔
      QuotientGroup.mk' NQ ⟨h * (x0 : F) * h⁻¹, hQnorm.conj_mem (x0 : F) x0.2 h⟩ =
        QuotientGroup.mk' NQ x0) := by
    intro h hhH
    have hha : h • a = a := MulAction.mem_stabilizer_iff.mp (hHa ▸ hhH)
    have haux : h • ((x0 : F) • a) =
        ((⟨h * (x0 : F) * h⁻¹, hQnorm.conj_mem (x0 : F) x0.2 h⟩ : ↥Q) : F) • a := by
      simp only [app3_1_smul_conj, hha]
    rw [MulAction.mem_stabilizer_iff, ← hx0, haux, key_mem]
  have key_final : ∀ h : F, h ∈ H →
      (QuotientGroup.mk' NQ ⟨h * q0 * h⁻¹, hQnorm.conj_mem q0 hq0Q h⟩ =
        QuotientGroup.mk' NQ ⟨q0, hq0Q⟩ ↔
      QuotientGroup.mk' NQ ⟨h * (x0 : F) * h⁻¹, hQnorm.conj_mem (x0 : F) x0.2 h⟩ =
        QuotientGroup.mk' NQ x0) := by
    intro h hhH
    have hβ : QuotientGroup.mk' NQ ⟨h * q0 * h⁻¹, hQnorm.conj_mem q0 hq0Q h⟩ =
        QuotientGroup.mk' NQ ⟨h * (x0 : F) * h⁻¹, hQnorm.conj_mem (x0 : F) x0.2 h⟩ *
        QuotientGroup.mk' NQ ⟨h * (x0 : F) * h⁻¹, hQnorm.conj_mem (x0 : F) x0.2 h⟩ := by
      have h1 : QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h (x0 * x0)) =
          QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h ⟨q0, hq0Q⟩) := by
        apply cjH_resp h hhH
        rw [map_mul]
        exact hv_eq
      have h2 : app3_1_conjQ Q hQnorm h x0 =
          ⟨h * (x0 : F) * h⁻¹, hQnorm.conj_mem (x0 : F) x0.2 h⟩ := rfl
      have h3 : app3_1_conjQ Q hQnorm h ⟨q0, hq0Q⟩ =
          ⟨h * q0 * h⁻¹, hQnorm.conj_mem q0 hq0Q h⟩ := rfl
      calc QuotientGroup.mk' NQ ⟨h * q0 * h⁻¹, hQnorm.conj_mem q0 hq0Q h⟩
          = QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h ⟨q0, hq0Q⟩) := by rw [h3]
        _ = QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h (x0 * x0)) := by rw [h1]
        _ = QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h x0 * app3_1_conjQ Q hQnorm h x0) := by
              rw [app3_1_conjQ_mul Q hQnorm]
        _ = QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h x0) *
              QuotientGroup.mk' NQ (app3_1_conjQ Q hQnorm h x0) := map_mul _ _ _
        _ = QuotientGroup.mk' NQ ⟨h * (x0 : F) * h⁻¹, hQnorm.conj_mem (x0 : F) x0.2 h⟩ *
              QuotientGroup.mk' NQ ⟨h * (x0 : F) * h⁻¹, hQnorm.conj_mem (x0 : F) x0.2 h⟩ := by
              rw [h2]
    constructor
    · intro hh
      refine app3_1_sq_eq_of_odd_card hVodd ?_
      rw [pow_two, pow_two, ← hβ, hh, ← hv_eq]
    · intro hh
      rw [hβ, hh, hv_eq]
  refine le_antisymm ?_ ?_
  · intro h hh
    obtain ⟨hhH, hhc⟩ := hh
    exact ⟨hhH, (hchar2 h hhH).mpr (key_final h hhH |>.mp ((hchar1 h hhH).mp hhc))⟩
  · intro h hh
    obtain ⟨hhH, hhb⟩ := hh
    exact ⟨hhH, (hchar1 h hhH).mpr (key_final h hhH |>.mpr ((hchar2 h hhH).mp hhb))⟩

/-! ## 3. Peterfalvi I Appendix III (1) -/

/-- **Peterfalvi I Appendix III (1) (p. 206).**  Let the finite group `F` act transitively on the
set `A`, let `H = Stab_F a` be a **maximal** subgroup of `F` and a proper Bender group of `F`
(`IsStronglyEmbedded`), and suppose `F` has 2-rank `1` (`¬ HasFourGroup F`).  If `t ∈ F` is an
involution outside `H` and `b` is the fixed point of `t` (assumed unique), then

`H ∩ H^t = H ∩ Stab_F b`,

i.e. the two-point stabiliser `H ∩ H^t` of the pair `(a, t • a)` is contained in the point
stabiliser of the fixed point of `t`.

(Source: `H ∩ H^t = H ∩ H(t)`.  The proof needs Appendix III (2) (`F = Q ⋊ H`, `Q` elementary
abelian, `C_H(Q) = 1`, via Brauer–Suzuki and Feit–Thompson) and (3) (`H` has a unique involution `u`,
and `D = H ∩ H^t` is centralised by `u` and `t`); both may be proved as helper results in the same
file.) -/
theorem app3_1 {F A : Type} [Group F] [Finite F] [MulAction F A] (a : A)
    (htrans : MulAction.IsPretransitive F A)
    (hstrong : LeanEval.GroupTheory.Defs.IsStronglyEmbedded (MulAction.stabilizer F a))
    (hmax : IsCoatom (MulAction.stabilizer F a))
    (hrank : ¬ Submission.Blueprint.HasFourGroup F)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hFT : Submission.Blueprint.FeitThompsonProp)
    {t : F} (ht : orderOf t = 2) (htH : t ∉ MulAction.stabilizer F a)
    {b : A} (hb : t • b = b) (hbuniq : ∀ c : A, t • c = c → c = b) :
    MulAction.stabilizer F a ⊓ Submission.Blueprint.conj t (MulAction.stabilizer F a) =
      MulAction.stabilizer F a ⊓ MulAction.stabilizer F b := by
  classical
  set H : Subgroup F := MulAction.stabilizer F a with hHdef
  -- an involution `u ∈ H`
  obtain ⟨u, huH, hu2⟩ := Work.ThreePoints.exists_orderOf_two_of_even_card (C := H) hstrong.2.1
  -- Peterfalvi I Ch. I §1 (2): the centraliser of an involution of `H` lies in `H`
  have hCuH : Subgroup.centralizer ({u} : Set F) ≤ H :=
    IsStronglyEmbedded.centralizer_le hstrong huH (by rw [hu2])
  -- Brauer–Suzuki: `F = O(F) · H`
  have hOH : Submission.Blueprint.oddCore F ⊔ H = ⊤ := by
    have h := sup_le_sup_left hCuH (Submission.Blueprint.oddCore F)
    rw [hBrSz F hrank u hu2] at h
    exact top_le_iff.mp h
  -- `O(F) ⊄ H`, since `H ≠ ⊤`
  have hOnotle : ¬ Submission.Blueprint.oddCore F ≤ H := by
    intro hle
    have htop : (⊤ : Subgroup F) ≤ H := by
      rw [← hOH]
      exact sup_le hle le_rfl
    exact hstrong.1 (hHdef ▸ top_le_iff.mp htop)
  -- `O(F)` is solvable of odd order (Feit–Thompson)
  have hOsolv : Group.IsSolvable ↥(Submission.Blueprint.oddCore F) :=
    hFT ↥(Submission.Blueprint.oddCore F) Work.BrauerSuzuki.OddCore.oddCard_oddCore
  -- the normal subgroup `Q ⊴ F` with `Q ⊄ H`, `Q ≤ O(F)` and `⁅Q,Q⁆ ≤ H`
  obtain ⟨Q, hQnorm, -, hQnotle, hQder, hQodd⟩ :=
    exists_normal_commutator_le (Submission.Blueprint.oddCore F) H
      (Work.BrauerSuzuki.oddCore_normal F) hOsolv
      Work.BrauerSuzuki.OddCore.oddCard_oddCore hOnotle
  -- maximality of `H`: `Q ⊔ H = ⊤`
  have hQH : Q ⊔ H = ⊤ := by
    refine hmax.2 (Q ⊔ H) ⟨le_sup_right, fun hle => hQnotle (le_trans le_sup_left hle)⟩
  have ht2 : t ^ 2 = 1 := by simpa [ht] using pow_orderOf_eq_one t
  have hres := app3_1_core (F := F) (A := A) (a := a) (b := b) (H := H) (Q := Q)
    htrans hHdef hQnorm hQH hQder hQodd ht2 hb hbuniq
  simpa [hHdef] using hres

end Work.ThreePoints.ThmC
