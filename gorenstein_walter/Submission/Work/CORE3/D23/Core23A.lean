import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.J4.J4U3ConjK
import Submission.Work.CORE3.J4U3V18Aux.PcoreConjCentralizer

/-!
# GW design pass 23, item A — Bender 1981 §3 step (7), `|U| = 3` (Case 1b)

Repaired proof (see `Submission/Work/NOTES_LEAD_gw_design23.md` §A).  The printed proof on
p. 224 reads "`F(U) ⊆ C_G(X) ⊆ N_G(X) ⊆ Ĥ^g`; and since `V^g ⊄ Ĥ` it follows that
`C_{F(U)}(V^g) = 1`, hence `|F(U)| = 3` and therefore `|U| = 3`" (the page image says
`C_{F(U)}(V^g)`, *not* `C_{Ĥ^g}(V^g)`; the OCR was wrong).  Everything after the first inclusion
is correct; the unjustified step is `F(U) ⊆ C_G(X)`.  It holds because of Bender's own
parenthetical on p. 223 ("`[Ĥ,s]` centralizes `F(U)`") **and the hypothesis that `N_Ĥ(X)` has
even order** (Bender prints `N_{Ĥ}(X)`; the Lean statement weakened it to `N_G(X)`, which is
automatic from `y` and useless):

* an involution `s ∈ Ĥ` inverting `X` exists (all three consumer sites construct one);
* all involutions of `Ĥ ∖ V` induce the same automorphism of `F(U)` (leaf `L1`);
* for `x ∈ X`, `r := x⁻¹ s x` is such an involution and `s * r = x²`, so `x²`, hence `x`
  (odd order), centralizes `F(U)`;
* `F(U) ≤ C_G(X) ≤ N_G(X) ≤ Ĥ^g` (`J4U3ConjK`), and `V^g ⊓ Ĥ = ⊥` (`PcoreConjCentralizer`);
  local control kills `C_{F(U)}(V^g)`, so `|F(U)| ∣ 3` (leaf `L3`); `K ≤ F(U)`, `K ≠ 1`;
* `|F(U)| = 3 ⟹ |U| = 3` (leaf `L4`: `U/C_U(F(U)) ↪ Aut(C₃)`, `C_U(F(U)) ≤ F(U)`).
-/

namespace Work.CORE3.D23

open Work.GW2

/-- **L1** (Bender p. 223 parenthetical, "`[Ĥ,s]` centralizes `F(U)`").  Two involutions of
`Ĥ ∖ V` act identically on `F(U)`.  Proof: `K = I_{F(U)}(r)` (`D.inv`, `K ≤ F(U)`), 1.5(ii)
(`I.T.c15` on `F(U)`) gives `|C_{F(U)}(r)| = |F(U) : K| =: n`, coprime to `|K|` (`D.hall`);
`K` is central in `F(U)` (`J4U3V18Aux.KCentralizesFittingU`), `K ⊓ C_{F(U)}(r) = 1` (odd), so
`F(U) = K × C_{F(U)}(r)` and `C_{F(U)}(r) = {f ∈ F(U) | f ^ n = 1}` — independent of `r`;
writing `f = k c`, `r f r⁻¹ = k⁻¹ c` for both `r`. -/
def InvolActionUniformProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (_I : Case1Inputs) (_h : BenderCtx G) (B : BenderSetup G)
    (_h1 : Case1 B) (_D : Case1bData B) (r₁ r₂ : G),
    r₁ ∈ B.Hhat → orderOf r₁ = 2 → r₁ ∉ pCoreIn 2 B.Hhat →
    r₂ ∈ B.Hhat → orderOf r₂ = 2 → r₂ ∉ pCoreIn 2 B.Hhat →
    ∀ f ∈ fittingIn B.U, r₁ * f * r₁⁻¹ = r₂ * f * r₂⁻¹

/-- **L3** (the correct part of Bender's printed (7)).  A subgroup `Y ≤ F(U)` lying in `Ĥ^g`,
with `V^g ⊓ Ĥ = ⊥`, has order dividing `3`.  Proof: `Y` normalizes `V^g = O₂(Ĥ^g)`
(conjugate `NormalizerPcoreEqHhat`); `C_Y(V^g)` is normalized by `V^g`, so if it is `≠ ⊥`
local control (`h1.2`) puts `V^g ≤ Ĥ`, contradicting `V^g ⊓ Ĥ = ⊥` and `|V^g| = 4`; hence `Y`
acts faithfully on the three involutions of `V^g`, `|Y| ∣ 6`, and `|Y|` is odd (`Y ≤ U`). -/
def FittingFaithfulFourProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (_I : Case1Inputs) (_h : BenderCtx G) (B : BenderSetup G)
    (_h1 : Case1 B) (_D : Case1bData B) (g : G) (Y : Subgroup G),
    Y ≤ fittingIn B.U → Y ≤ conjSub g B.Hhat →
    conjSub g (pCoreIn 2 B.Hhat) ⊓ B.Hhat = ⊥ → Nat.card Y ∣ 3

/-- **L4**.  `|F(U)| = 3 ⟹ |U| = 3`: `U` (odd) acts on `F(U) ≅ C₃` with image in `Aut(C₃)` of
order 2, so `U = C_U(F(U)) ≤ F(U)` (`OddOrder.GroupTheory.centralizer_fitting_le_fitting`,
FT via `I.T.ft`; cf. `CORE2B/HallAux.lean:277`). -/
def CardUOfFittingThreeProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (_I : Case1Inputs) (_h : BenderCtx G) (B : BenderSetup G)
    (_h1 : Case1 B) (_D : Case1bData B),
    Nat.card (fittingIn B.U) = 3 → Nat.card B.U = 3

/-- Pure algebra: if `s² = 1`, `s x s⁻¹ = x⁻¹` and `s` and `x⁻¹ s x` conjugate `f` the same way,
then `x²` commutes with `f`. -/
theorem sq_commute_of_uniform {G : Type} [Group G] {s x f : G} (hs : s * s = 1)
    (hsx : s * x * s⁻¹ = x⁻¹)
    (hu : s * f * s⁻¹ = (x⁻¹ * s * x) * f * (x⁻¹ * s * x)⁻¹) :
    x ^ 2 * f = f * x ^ 2 := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hr : x⁻¹ * s * x = s * x ^ 2 := by
    have h1 : x⁻¹ = s * x * s := by rw [← hsx, hsi]
    rw [h1, pow_two]
    calc s * x * s * s * x = s * x * (s * s) * x := by group
      _ = s * (x * x) := by rw [hs]; group
  rw [hr] at hu
  have h2 : f = x ^ 2 * f * (x ^ 2)⁻¹ := by
    have h3 : s⁻¹ * (s * f * s⁻¹) * s = s⁻¹ * (s * x ^ 2 * f * (s * x ^ 2)⁻¹) * s := by rw [hu]
    simpa [mul_assoc, mul_inv_rev] using h3
  calc x ^ 2 * f = x ^ 2 * f * (x ^ 2)⁻¹ * x ^ 2 := by group
    _ = f * x ^ 2 := by rw [← h2]

/-- An element of odd order is a power of its square. -/
theorem commute_of_sq_commute_odd {G : Type} [Group G] {x f : G} (hodd : Odd (orderOf x))
    (h : x ^ 2 * f = f * x ^ 2) : x * f = f * x := by
  obtain ⟨m, hm⟩ := hodd
  have hx : x = (x ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hc : Commute (x ^ 2) f := h
  have := hc.pow_left (m + 1)
  rw [← hx] at this
  exact this

/-- **Assembly: Bender (7), `|U| = 3`, with Bender's `N_Ĥ(X)`-hypothesis** in the form "some
involution `s ∈ Ĥ` inverts `X`".  Uses only sorry-free in-tree results besides the three
leaves. -/
theorem J4U3V18s (hL1 : InvolActionUniformProp) (hL3 : FittingFaithfulFourProp)
    (hL4 : CardUOfFittingThreeProp)
    (G : Type) [Group G] [Finite G] (I : Case1Inputs) (h : BenderCtx G)
    (B : BenderSetup G) (h1 : Case1 B) (D : Case1bData B) {y : G} (hy2 : orderOf y = 2)
    (hyH : y ∉ B.Hhat) (X : Subgroup G) (hXle : X ≤ B.Hhat) (hXne : X ≠ ⊥)
    (hXodd : Odd (Nat.card X)) (hinv : Inverts y X)
    (hCeven : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    {s : G} (hsH : s ∈ B.Hhat) (hs2 : orderOf s = 2) (hsX : Inverts s X) :
    Nat.card B.U = 3 := by
  classical
  -- the conjugate `Ĥ^g` and `V^g ⊓ Ĥ = ⊥`
  obtain ⟨g, hK, hN⟩ := J4.J4U3ConjK I h B h1 D hy2 hyH hXle hXne hXodd hinv hCeven
  obtain ⟨-, hVg⟩ := J4U3V18Aux.PcoreConjCentralizer I h B h1 D hy2 hyH X hXle hXne hXodd hinv
    hCeven g hK hN
  have hs : s * s = 1 := ((orderOf_eq_two_iff_mul_self s).mp hs2).1
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  -- `V = O₂(Ĥ)` is normal in `Ĥ`
  have hNV := NormalizerPcoreEqHhat G h B D.four
  have hVnorm : ∀ a ∈ B.Hhat, ∀ v ∈ pCoreIn 2 B.Hhat, a * v * a⁻¹ ∈ pCoreIn 2 B.Hhat := by
    intro a ha v hv
    have ha' : a ∈ Subgroup.normalizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
      rw [hNV]; exact ha
    exact (Subgroup.mem_normalizer_iff.mp ha' v).mp hv
  -- odd orders of elements of `X`
  have hoddx : ∀ x ∈ X, Odd (orderOf x) := by
    intro x hx
    have hd : orderOf (⟨x, hx⟩ : X) ∣ Nat.card X := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hd
    exact hXodd.of_dvd_nat hd
  -- `s ∉ V`: otherwise every `x ∈ X` has `x² ∈ V`, hence `x ∈ V`, and `X` odd forces `X = ⊥`
  have hsV : s ∉ pCoreIn 2 B.Hhat := by
    intro hsV
    apply hXne
    rw [eq_bot_iff]
    intro x hx
    have hxH : x ∈ B.Hhat := hXle hx
    have hsxs : s * x * s⁻¹ = x⁻¹ := hsX x hx
    -- `(x s x⁻¹) * s = x²`
    have h1 : x * s * x⁻¹ * s = x ^ 2 := by
      have : s * x⁻¹ * s⁻¹ = x := by
        have := congrArg (·⁻¹) hsxs; simpa [mul_assoc, mul_inv_rev] using this
      rw [pow_two]
      calc x * s * x⁻¹ * s = x * (s * x⁻¹ * s⁻¹) := by rw [hsi]; group
        _ = x * x := by rw [this]
    have hx2V : x ^ 2 ∈ pCoreIn 2 B.Hhat := by
      rw [← h1]; exact Subgroup.mul_mem _ (hVnorm x hxH s hsV) hsV
    -- `x = (x²)^(m+1)` lies in `V`
    obtain ⟨m, hm⟩ := hoddx x hx
    have hxeq : x = (x ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    have hxV : x ∈ pCoreIn 2 B.Hhat := by rw [hxeq]; exact Subgroup.pow_mem _ hx2V _
    -- `x ∈ X ⊓ V`, a group of odd order dividing `4`
    have hxo2 : orderOf x ∣ 4 := by
      have := orderOf_dvd_natCard (⟨x, hxV⟩ : pCoreIn 2 B.Hhat)
      rw [Subgroup.orderOf_mk, D.four.1] at this
      exact this
    have hxo : orderOf x = 1 := by
      obtain ⟨k, hk⟩ := hoddx x hx
      have : orderOf x ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hxo2, by norm_num⟩
      have h4 : Nat.divisors 4 = {1, 2, 4} := by decide
      rw [h4] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      omega
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hxo)
  -- `F(U) ≤ C_G(X)`
  have hFC : ∀ f ∈ fittingIn B.U, ∀ x ∈ X, x * f = f * x := by
    intro f hf x hx
    have hxH : x ∈ B.Hhat := hXle hx
    have hsxs : s * x * s⁻¹ = x⁻¹ := hsX x hx
    have hrH : x⁻¹ * s * x ∈ B.Hhat :=
      B.Hhat.mul_mem (B.Hhat.mul_mem (B.Hhat.inv_mem hxH) hsH) hxH
    have hr2 : orderOf (x⁻¹ * s * x) = 2 := by
      have : x⁻¹ * s * x = (MulAut.conj x⁻¹) s := by simp [MulAut.conj_apply]
      rw [this, MulEquiv.orderOf_eq]; exact hs2
    have hrV : x⁻¹ * s * x ∉ pCoreIn 2 B.Hhat := by
      intro hr
      apply hsV
      have := hVnorm x hxH _ hr
      simpa [mul_assoc] using this
    have hu := hL1 G I h B h1 D s (x⁻¹ * s * x) hsH hs2 hsV hrH hr2 hrV f hf
    exact commute_of_sq_commute_odd (hoddx x hx) (sq_commute_of_uniform hs hsxs hu)
  -- `F(U) ≤ N_G(X) ≤ Ĥ^g`
  have hFle : fittingIn B.U ≤ conjSub g B.Hhat := by
    intro f hf
    apply hN
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : f * x * f⁻¹ = x := by rw [← hFC f hf x hx]; group
      rw [this]; exact hx
    · intro hx
      -- `f x f⁻¹ ∈ X`; then `x = f⁻¹ (f x f⁻¹) f = f x f⁻¹`
      have h2 := hFC f hf _ hx
      have h3 : f * x = f * (f * x * f⁻¹) := by
        rw [← h2]; group
      have : x = f * x * f⁻¹ := mul_left_cancel h3
      rw [this]; exact hx
  have hdvd : Nat.card (fittingIn B.U) ∣ 3 := hL3 G I h B h1 D g _ le_rfl hFle hVg
  -- `|F(U)| ≠ 1` since `1 ≠ K ≤ F(U)`
  have hF1 : Nat.card (fittingIn B.U) ≠ 1 := by
    intro h1'
    apply D.ne
    rw [eq_bot_iff]
    intro k hk
    have hkF : k ∈ fittingIn B.U := D.hall.1 hk
    have : fittingIn B.U = ⊥ := Subgroup.card_eq_one.mp h1'
    rw [this] at hkF
    exact hkF
  have hF3 : Nat.card (fittingIn B.U) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h' | h'
    · exact absurd h' hF1
    · exact h'
  exact hL4 G I h B h1 D hF3

end Work.CORE3.D23
