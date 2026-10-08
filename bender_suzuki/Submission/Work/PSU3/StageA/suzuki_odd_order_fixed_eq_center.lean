import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.typeB
import Submission.Work.Higman.Basic
import Submission.Work.Higman.Layers.card_dvd_card_sub_one_of_map_xi_eq
import Submission.Work.Higman.LayersAlt.GroupSide
import Submission.Work.Higman.Layers.finrank_eq_n_of_isInv_ne

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.PSU3.StageA

open Work.Higman
open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

/-- Some representative of a coset modulo a normal subgroup. -/
theorem exists_mk_eq {G : Type} [Group G] (N : Subgroup G) [N.Normal] (q : G ⧸ N) :
    ∃ y : G, (QuotientGroup.mk y : G ⧸ N) = q := by
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N q
  exact ⟨y, by rwa [QuotientGroup.mk'_apply] at hy⟩

/-- **Squares are well-defined on `P ⧸ Z(P)`.**  If `x⁻¹ y` is central then `x² = y²`:
write `y = x z` with `z` central; then `y² = x² z² = x²` because `z² = 1`. -/
theorem sq_eq_sq_of_mem_center_mul {hzsq : ∀ z : P, z ∈ Subgroup.center P → z ^ 2 = 1}
    {x y : P} (hmem : x⁻¹ * y ∈ Subgroup.center P) : x * x = y * y := by
  set z := x⁻¹ * y with hz
  have hy : y = x * z := by rw [hz]; group
  have hzc : x * z = z * x := Subgroup.mem_center_iff.mp hmem x
  have hz2 : z * z = 1 := by simpa [pow_two] using hzsq z hmem
  have key : (x * z) * (x * z) = x * x := by
    calc (x * z) * (x * z) = x * (z * x) * z := by group
      _ = x * (x * z) * z := by rw [hzc]
      _ = (x * x) * (z * z) := by group
      _ = x * x := by rw [hz2, mul_one]
  rw [hy, key]

/-- `quotMulEquiv` is multiplicative in the automorphism argument. -/
theorem quotMulEquiv_mul (h : IsSuzuki2Grp P) (A B : MulAut P) :
    LayersAlt.quotMulEquiv h (A * B) =
      LayersAlt.quotMulEquiv h A * LayersAlt.quotMulEquiv h B := by
  ext q
  obtain ⟨y, hy⟩ := exists_mk_eq (Subgroup.center P) q
  rw [← hy]
  show LayersAlt.quotMulEquiv h (A * B) (QuotientGroup.mk y) =
    (LayersAlt.quotMulEquiv h A * LayersAlt.quotMulEquiv h B) (QuotientGroup.mk y)
  rw [MulAut.mul_apply, LayersAlt.quotMulEquiv_mk, LayersAlt.quotMulEquiv_mk,
    LayersAlt.quotMulEquiv_mk, MulAut.mul_apply]

/-- `quotMulEquiv` sends `1` to `1`. -/
theorem quotMulEquiv_one (h : IsSuzuki2Grp P) :
    LayersAlt.quotMulEquiv h (1 : MulAut P) = 1 := by
  ext q
  obtain ⟨y, hy⟩ := exists_mk_eq (Subgroup.center P) q
  rw [← hy]
  show LayersAlt.quotMulEquiv h (1 : MulAut P) (QuotientGroup.mk y) =
    (1 : P ⧸ Subgroup.center P ≃* P ⧸ Subgroup.center P) (QuotientGroup.mk y)
  rw [LayersAlt.quotMulEquiv_mk]
  rfl

theorem quotMulEquiv_pow (h : IsSuzuki2Grp P) (A : MulAut P) (k : ℕ) :
    (LayersAlt.quotMulEquiv h A) ^ k = LayersAlt.quotMulEquiv h (A ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact (quotMulEquiv_one h).symm
  | succ k ih => rw [pow_succ, pow_succ, ih, ← quotMulEquiv_mul]

theorem suzuki_odd_order_fixed_eq_center {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {ξ : MulAut P} (hξ : Work.Higman.FpfXi ξ)
    (hsq : ∀ x : P, x ^ 2 ∈ Subgroup.center P)
    (hzsq : ∀ z : P, z ∈ Subgroup.center P → z ^ 2 = 1)
    (hcomm : ∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center P)
    {A : MulAut P} (hodd : Odd (orderOf A)) (hAc : A * ξ = ξ * A)
    (hAfix : ∀ z ∈ Subgroup.center P, A z = z) (hA1 : A ≠ 1) :
    ∀ x : P, A x = x → x ∈ Subgroup.center P := by
  classical
  -- ### commutators are central
  have hcm : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    show ⁅x, y⁆ ∈ Subgroup.center P
    rw [commutatorElement_def]
    exact hcomm x y
  -- ### `V = P ⧸ Z(P)` as an `𝔽₂`-vector space
  letI : CommGroup (P ⧸ Subgroup.center P) :=
    { (inferInstance : Group (P ⧸ Subgroup.center P)) with
      mul_comm := LayersAlt.quot_mul_comm hcm }
  have hexp : ∀ x : Additive (P ⧸ Subgroup.center P), 2 • x = 0 := by
    intro x
    obtain ⟨v, rfl⟩ : ∃ v, Additive.ofMul v = x := ⟨Additive.toMul x, by simp⟩
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Subgroup.center P) v
    have hv : v * v = 1 := by
      rw [← hy, (map_mul (QuotientGroup.mk' (Subgroup.center P)) y y).symm,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      simpa [pow_two] using hsq y
    rw [two_nsmul, ← ofMul_mul, hv]; rfl
  haveI : Module (ZMod 2) (Additive (P ⧸ Subgroup.center P)) := AddCommGroup.zmodModule hexp
  haveI : Module.Finite (ZMod 2) (Additive (P ⧸ Subgroup.center P)) := Module.Finite.of_finite
  -- ### the two automorphisms of `V`
  let σe : Additive (P ⧸ Subgroup.center P) ≃+ Additive (P ⧸ Subgroup.center P) :=
    (LayersAlt.quotMulEquiv h ξ).toAdditive
  have hσsmul : ∀ (c : ZMod 2) (x : Additive (P ⧸ Subgroup.center P)),
      σe (c • x) = c • σe x := by
    intro c x
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl <;> simp
  let σ : Additive (P ⧸ Subgroup.center P) ≃ₗ[ZMod 2] Additive (P ⧸ Subgroup.center P) :=
    σe.toLinearEquiv hσsmul
  let Āe : Additive (P ⧸ Subgroup.center P) ≃+ Additive (P ⧸ Subgroup.center P) :=
    (LayersAlt.quotMulEquiv h A).toAdditive
  have hĀsmul : ∀ (c : ZMod 2) (x : Additive (P ⧸ Subgroup.center P)),
      Āe (c • x) = c • Āe x := by
    intro c x
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl <;> simp
  let Ā : Additive (P ⧸ Subgroup.center P) ≃ₗ[ZMod 2] Additive (P ⧸ Subgroup.center P) :=
    Āe.toLinearEquiv hĀsmul
  have hσmk : ∀ y : P, σ (Additive.ofMul (QuotientGroup.mk y)) =
      Additive.ofMul (QuotientGroup.mk (ξ y)) := by
    intro y
    show Additive.ofMul ((LayersAlt.quotMulEquiv h ξ) (QuotientGroup.mk y)) = _
    rw [LayersAlt.quotMulEquiv_mk]
  have hĀmk : ∀ y : P, Ā (Additive.ofMul (QuotientGroup.mk y)) =
      Additive.ofMul (QuotientGroup.mk (A y)) := by
    intro y
    show Additive.ofMul ((LayersAlt.quotMulEquiv h A) (QuotientGroup.mk y)) = _
    rw [LayersAlt.quotMulEquiv_mk]
  have hσpow : ∀ (k : ℕ) (y : P), (σ ^ k) (Additive.ofMul (QuotientGroup.mk y)) =
      Additive.ofMul (QuotientGroup.mk ((ξ ^ k) y)) := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
        intro y
        rw [pow_succ', LinearEquiv.mul_apply, ih, hσmk, pow_succ', MulAut.mul_apply]
  have hĀpow : ∀ (k : ℕ) (y : P), (Ā ^ k) (Additive.ofMul (QuotientGroup.mk y)) =
      Additive.ofMul (QuotientGroup.mk ((A ^ k) y)) := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
        intro y
        rw [pow_succ', LinearEquiv.mul_apply, ih, hĀmk, pow_succ', MulAut.mul_apply]
  have hσĀcomm : Ā * σ = σ * Ā := by
    ext x
    obtain ⟨y, hy⟩ := exists_mk_eq (Subgroup.center P) (Additive.toMul x)
    have hx : x = Additive.ofMul (QuotientGroup.mk y) := by rw [hy]; rfl
    rw [hx, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hσmk, hĀmk, hĀmk, hσmk]
    rw [show A (ξ y) = ξ (A y) from by
      have hh := congrArg (fun f : MulAut P => f y) hAc
      simpa [MulAut.mul_apply] using hh]
  -- ### `pow = 1` dictionaries
  have hσ_pow_eq_one : ∀ k : ℕ, σ ^ k = 1 ↔ (LayersAlt.quotMulEquiv h ξ) ^ k = 1 := by
    intro k
    constructor
    · intro h1
      ext q
      obtain ⟨y, hy⟩ := exists_mk_eq (Subgroup.center P) q
      rw [← hy, LayersAlt.quotMulEquiv_pow_mk]
      have h2 : (σ ^ k) (Additive.ofMul (QuotientGroup.mk y)) =
          Additive.ofMul (QuotientGroup.mk y) := by rw [h1]; rfl
      rw [hσpow] at h2
      exact Additive.ofMul.injective h2
    · intro h1
      ext x
      obtain ⟨y, hy⟩ := exists_mk_eq (Subgroup.center P) (Additive.toMul x)
      have hx : x = Additive.ofMul (QuotientGroup.mk y) := by rw [hy]; rfl
      rw [hx, hσpow, ← LayersAlt.quotMulEquiv_pow_mk, h1]
      rfl
  have hĀ_pow_eq_one : ∀ k : ℕ, Ā ^ k = 1 ↔ (LayersAlt.quotMulEquiv h A) ^ k = 1 := by
    intro k
    constructor
    · intro h1
      ext q
      obtain ⟨y, hy⟩ := exists_mk_eq (Subgroup.center P) q
      rw [← hy, LayersAlt.quotMulEquiv_pow_mk]
      have h2 : (Ā ^ k) (Additive.ofMul (QuotientGroup.mk y)) =
          Additive.ofMul (QuotientGroup.mk y) := by rw [h1]; rfl
      rw [hĀpow] at h2
      exact Additive.ofMul.injective h2
    · intro h1
      ext x
      obtain ⟨y, hy⟩ := exists_mk_eq (Subgroup.center P) (Additive.toMul x)
      have hx : x = Additive.ofMul (QuotientGroup.mk y) := by rw [hy]; rfl
      rw [hx, hĀpow, ← LayersAlt.quotMulEquiv_pow_mk, h1]
      rfl
  -- ### order data for `σ`
  obtain ⟨N, hN⟩ : ∃ N, Nat.card ↥(Subgroup.center P) = 2 ^ N :=
    (IsPGroup.iff_card).mp (h.isPGroup.to_subgroup (Subgroup.center P))
  obtain ⟨hordσe, hfpfσe, hcardVq, hN1⟩ := LayersAlt.quotMulEquiv_props h hξ hN
  have hσpowLin : ∀ k : ℕ, (σ ^ k).toLinearMap = σ.toLinearMap ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, LinearEquiv.coe_toLinearMap_one]; rfl
    | succ k ih => rw [pow_succ, pow_succ, LinearEquiv.coe_toLinearMap_mul, ih]
  have hord_toLin : orderOf σ.toLinearMap = orderOf σ := by
    refine Nat.dvd_antisymm ?_ ?_
    · rw [orderOf_dvd_iff_pow_eq_one, ← hσpowLin (orderOf σ)]
      rw [pow_orderOf_eq_one, LinearEquiv.coe_toLinearMap_one]
      rfl
    · rw [orderOf_dvd_iff_pow_eq_one]
      apply LinearEquiv.toLinearMap_injective
      rw [hσpowLin, LinearEquiv.coe_toLinearMap_one]
      exact pow_orderOf_eq_one _
  have hord_σ : orderOf σ = 2 ^ N - 1 := by
    refine Nat.dvd_antisymm ?_ ?_
    · rw [orderOf_dvd_iff_pow_eq_one, (hσ_pow_eq_one (2 ^ N - 1)), ← hordσe]
      exact pow_orderOf_eq_one _
    · rw [← hordσe, orderOf_dvd_iff_pow_eq_one]
      exact (hσ_pow_eq_one _).mp (pow_orderOf_eq_one σ)
  have hordσ : orderOf σ.toLinearMap = 2 ^ N - 1 := hord_toLin.trans hord_σ
  have hcardV : Nat.card (Additive (P ⧸ Subgroup.center P)) = 2 ^ (2 * N) := by
    rw [Nat.card_congr (Additive.toMul (α := P ⧸ Subgroup.center P)), hcardVq, ← pow_mul,
      Nat.mul_comm]
  have hsr : Layers.Semiregular σ.toLinearMap := by
    intro k v hv hfix
    obtain ⟨y, hy⟩ := exists_mk_eq (Subgroup.center P) (Additive.toMul v)
    have hv' : v = Additive.ofMul (QuotientGroup.mk y) := by rw [hy]; rfl
    have hy1 : QuotientGroup.mk y ≠ (1 : P ⧸ Subgroup.center P) := by
      intro hc; exact hv (by rw [hv', hc]; rfl)
    have hfixv : (σ ^ k) v = v := by
      rw [← hσpowLin k] at hfix
      exact hfix
    rw [hv', hσpow] at hfixv
    have hyk : (LayersAlt.quotMulEquiv h ξ ^ k) (QuotientGroup.mk y) =
        QuotientGroup.mk y := by
      rw [LayersAlt.quotMulEquiv_pow_mk]
      exact Additive.ofMul.injective hfixv
    have hq1 : LayersAlt.quotMulEquiv h ξ ^ k = 1 := by
      by_contra hc
      exact hfpfσe k hc (QuotientGroup.mk y) hy1 hyk
    have hσ1 : σ ^ k = 1 := (hσ_pow_eq_one k).mpr hq1
    rw [← hσpowLin k, hσ1]
    rfl
  -- ### `Odd (orderOf Ā)`
  have hoddĀ : Odd (orderOf Ā) :=
    Odd.of_dvd_nat hodd (orderOf_dvd_iff_pow_eq_one.mpr (by
      rw [hĀ_pow_eq_one, quotMulEquiv_pow, pow_orderOf_eq_one, quotMulEquiv_one]))
  -- ### `Ā ≠ 1`
  have hĀ_ne : Ā ≠ 1 := by
    intro hĀ1
    apply hA1
    have hA2 : A * A = 1 := by
      ext z
      have hmk : (QuotientGroup.mk (A z) : P ⧸ Subgroup.center P) = QuotientGroup.mk z := by
        have h1 : LayersAlt.quotMulEquiv h A (QuotientGroup.mk z) = QuotientGroup.mk z := by
          rw [LayersAlt.quotMulEquiv_mk]
          have h2 := congrArg (fun (f : Additive (P ⧸ Subgroup.center P) ≃ₗ[ZMod 2] _) =>
            f (Additive.ofMul (QuotientGroup.mk z))) hĀ1
          rw [hĀmk] at h2
          exact Additive.ofMul.injective h2
        rwa [LayersAlt.quotMulEquiv_mk] at h1
      have hzZ : ((A z)⁻¹ * z) ∈ Subgroup.center P := QuotientGroup.eq.mp hmk
      set w := (A z)⁻¹ * z with hw
      have hAz : A z = z * w⁻¹ := by rw [hw]; group
      have hwZ' : w⁻¹ ∈ Subgroup.center P := (Subgroup.center P).inv_mem hzZ
      have hw2 : w⁻¹ * w⁻¹ = 1 := by
        have := hzsq w⁻¹ hwZ'; simpa [pow_two] using this
      calc A (A z) = A (z * w⁻¹) := by rw [hAz]
        _ = A z * A w⁻¹ := by rw [map_mul]
        _ = (z * w⁻¹) * w⁻¹ := by rw [hAz, hAfix w⁻¹ hwZ']
        _ = z * (w⁻¹ * w⁻¹) := by group
        _ = z := by rw [hw2, mul_one]
    have hdvd : orderOf A ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact hA2
    obtain ⟨m, hm⟩ := hodd
    have hle2 : orderOf A ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have : orderOf A = 1 := by omega
    exact orderOf_eq_one_iff.mp this
  -- ### main argument
  intro x hAx
  by_contra hxZ
  set v : Additive (P ⧸ Subgroup.center P) := Additive.ofMul (QuotientGroup.mk x) with hv
  have hv_ne : v ≠ 0 := by
    intro hc
    apply hxZ
    have h1 : (QuotientGroup.mk x : P ⧸ Subgroup.center P) = 1 := by
      rw [hv] at hc
      exact ofMul_eq_zero.mp hc
    exact (QuotientGroup.eq_one_iff x).mp h1
  have hĀv : Ā v = v := by rw [hv, hĀmk, hAx]
  -- ### `W = ker (Ā - 1)` and `U = im (Ā - 1)`
  set T : Additive (P ⧸ Subgroup.center P) →ₗ[ZMod 2] Additive (P ⧸ Subgroup.center P) :=
    Ā.toLinearMap - 1 with hT
  set W : Submodule (ZMod 2) (Additive (P ⧸ Subgroup.center P)) := T.ker with hWdef
  set U : Submodule (ZMod 2) (Additive (P ⧸ Subgroup.center P)) := T.range with hUdef
  have hWmem : ∀ y, y ∈ W ↔ Ā y = y := by
    intro y
    rw [hWdef, LinearMap.mem_ker, hT]
    simp only [LinearMap.sub_apply, LinearEquiv.coe_toLinearMap]
    exact sub_eq_zero
  have hUmem : ∀ y, y ∈ U ↔ ∃ z, Ā z - z = y := by
    intro y
    rw [hUdef, LinearMap.mem_range, hT]
    simp only [LinearMap.sub_apply, LinearEquiv.coe_toLinearMap]
    simp
  have hWne : W ≠ ⊥ :=
    Submodule.ne_bot_iff W |>.mpr ⟨v, (hWmem v).mpr hĀv, hv_ne⟩
  have hWne_top : W ≠ ⊤ := by
    intro hWt
    apply hĀ_ne
    have h0 : T = 0 := LinearMap.ker_eq_top.mp (by rw [← hWdef]; exact hWt)
    rw [hT] at h0
    have h1 : Ā.toLinearMap = 1 := sub_eq_zero.mp h0
    exact LinearEquiv.toLinearMap_injective
      (by rw [h1, LinearEquiv.coe_toLinearMap_one]; rfl)
  have hUne : U ≠ ⊥ := by
    have hne : ∃ z : Additive (P ⧸ Subgroup.center P), Ā z ≠ z := by
      by_contra hcon
      push Not at hcon
      exact hĀ_ne (LinearEquiv.ext hcon)
    obtain ⟨z, hz⟩ := hne
    exact Submodule.ne_bot_iff U |>.mpr ⟨Ā z - z, (hUmem _).mpr ⟨z, rfl⟩, sub_ne_zero.mpr hz⟩
  have hUne_top : U ≠ ⊤ := by
    intro hUt
    apply hWne
    have hsurj : Function.Surjective T :=
      LinearMap.range_eq_top.mp (by rw [← hUdef]; exact hUt)
    rw [hWdef]
    exact LinearMap.ker_eq_bot.mpr
      ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mpr hsurj)
  have hcommLM : Ā.toLinearMap * σ.toLinearMap = σ.toLinearMap * Ā.toLinearMap := by
    have := congrArg LinearEquiv.toLinearMap hσĀcomm
    simpa [LinearEquiv.coe_toLinearMap_mul] using this
  have hcross : ∀ y, Ā (σ.toLinearMap y) = σ.toLinearMap (Ā y) := by
    intro y
    have h1 : (Ā.toLinearMap * σ.toLinearMap) y = (σ.toLinearMap * Ā.toLinearMap) y :=
      LinearMap.congr_fun hcommLM y
    rw [Module.End.mul_apply, Module.End.mul_apply] at h1
    exact h1
  have hWinv : Layers.IsInv σ.toLinearMap W := by
    intro y hy
    rw [hWmem] at hy ⊢
    rw [hcross, hy]
  have hUinv : Layers.IsInv σ.toLinearMap U := by
    intro y hy
    rw [hUmem] at hy ⊢
    obtain ⟨z, rfl⟩ := hy
    exact ⟨σ.toLinearMap z, by rw [map_sub, hcross z]⟩
  have hĀU : ∀ y ∈ U, Ā y ∈ U := by
    intro y hy
    rw [hUmem] at hy ⊢
    obtain ⟨z, rfl⟩ := hy
    exact ⟨Ā z, by rw [map_sub]⟩
  have hWU : W ⊓ U = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    rw [Submodule.mem_inf, hWmem] at hy
    obtain ⟨hyW, hyU⟩ := hy
    rw [hUmem] at hyU
    obtain ⟨z, hz⟩ := hyU
    have hz' : Ā z = z + y := by
      have h := hz
      rw [sub_eq_iff_eq_add'] at h
      exact h
    have hsq : (Ā * Ā) z = z := by
      have hzy : z + y + y = z := by
        rw [show z + y + y = z + 2 • y from by rw [two_nsmul]; abel, hexp, add_zero]
      rw [LinearEquiv.mul_apply, hz', map_add, hyW, hz']
      exact hzy
    obtain ⟨m, hm⟩ := hoddĀ
    have hpow2 : ∀ k : ℕ, ((Ā ^ 2) ^ k) z = z := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, LinearEquiv.mul_apply, show (Ā ^ 2) z = z from hsq, ih]
    have hAeq : Ā z = z := by
      have h4 : ((Ā ^ 2) ^ m) * Ā = 1 := by
        have h5 : Ā ^ (2 * m) * Ā = 1 := by
          rw [← pow_succ, ← hm]
          exact pow_orderOf_eq_one Ā
        rwa [pow_mul] at h5
      have h3 : Ā = ((Ā ^ 2) ^ m)⁻¹ := eq_inv_of_mul_eq_one_right h4
      calc Ā z = ((Ā ^ 2) ^ m)⁻¹ z := congrArg (fun f : Additive (P ⧸ Subgroup.center P) ≃ₗ[ZMod 2] _ => f z) h3
        _ = ((Ā ^ 2) ^ m)⁻¹ (((Ā ^ 2) ^ m) z) := by rw [hpow2]
        _ = z := by rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
    rw [← hz, hAeq, sub_self]
  -- ### finrank / cardinality of `U`
  have hWfr : Module.finrank (ZMod 2) ↥W = N :=
    Layers.finrank_eq_n_of_isInv_ne hN1 hcardV hordσ hsr hWinv hWne hWne_top
  have hUfr : Module.finrank (ZMod 2) ↥U = N :=
    Layers.finrank_eq_n_of_isInv_ne hN1 hcardV hordσ hsr hUinv hUne hUne_top
  have hUcard : Nat.card ↥U = 2 ^ N := by
    haveI : Module.Finite (ZMod 2) ↥U := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥U), Nat.card_zmod, hUfr]
  -- ### `σ` is transitive on `U ∖ {0}`
  obtain ⟨w, hwU, hw0⟩ : ∃ w ∈ U, w ≠ 0 := Submodule.ne_bot_iff U |>.mp hUne
  have hpowU : ∀ i : ℕ, (σ ^ i) w ∈ U := by
    intro i
    induction i with
    | zero => simpa using hwU
    | succ i ih => rw [pow_succ', LinearEquiv.mul_apply]; exact hUinv _ ih
  haveI : Fintype ↥U := Fintype.ofFinite ↥U
  obtain ⟨yy, hyy⟩ := exists_mk_eq (Subgroup.center P) (Additive.toMul w)
  have hwrepr : w = Additive.ofMul (QuotientGroup.mk yy) := by rw [hyy]; rfl
  have hwne : Additive.toMul w ≠ (1 : P ⧸ Subgroup.center P) := by
    intro hc; exact hw0 (by rw [hwrepr, hyy, hc]; rfl)
  have htrans : ∀ y : Additive (P ⧸ Subgroup.center P), y ∈ U → y ≠ 0 →
      ∃ k : ℕ, (σ ^ k) w = y := by
    intro y hyU hy0
    have hcardU' : Fintype.card ↥U = 2 ^ N := by rw [← Nat.card_eq_fintype_card]; exact hUcard
    have hinj : Function.Injective
        (fun i : Fin (2 ^ N - 1) => (⟨(σ ^ (i : ℕ)) w, hpowU (i : ℕ)⟩ : ↥U)) := by
      intro i j hij
      have h1 : (σ ^ (i : ℕ)) w = (σ ^ (j : ℕ)) w := congrArg Subtype.val hij
      rcases lt_trichotomy (i:ℕ) (j:ℕ) with hlt | heq | hgt
      · exfalso
        have h2 : (σ ^ ((j:ℕ) - (i:ℕ))) w = w := by
          have h3 : (σ ^ (i:ℕ)) ((σ ^ ((j:ℕ) - (i:ℕ))) w) = (σ ^ (i:ℕ)) w := by
            rw [← LinearEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' (le_of_lt hlt), h1]
          exact (σ ^ (i:ℕ)).injective h3
        have h4 : ((LayersAlt.quotMulEquiv h ξ) ^ ((j:ℕ) - (i:ℕ))) (Additive.toMul w) =
            Additive.toMul w := by
          rw [hwrepr] at h2
          rw [hσpow] at h2
          rw [← hyy, LayersAlt.quotMulEquiv_pow_mk]
          exact Additive.ofMul.injective h2
        have hdiv0 : orderOf (LayersAlt.quotMulEquiv h ξ) ∣ (j:ℕ) - (i:ℕ) :=
          orderOf_dvd_iff_pow_eq_one.mpr (by
            by_contra hc
            exact hfpfσe _ hc _ hwne h4)
        have hdiv : 2 ^ N - 1 ∣ (j:ℕ) - (i:ℕ) := by rwa [hordσe] at hdiv0
        have hlt' : (j:ℕ) - (i:ℕ) < 2 ^ N - 1 := lt_of_le_of_lt (Nat.sub_le _ _) j.isLt
        rcases Nat.eq_zero_or_pos ((j:ℕ)-(i:ℕ)) with h0 | hpos
        · omega
        · exact absurd (Nat.le_of_dvd hpos hdiv) (not_le.mpr hlt')
      · exact Fin.ext heq
      · exfalso
        have h2 : (σ ^ ((i:ℕ) - (j:ℕ))) w = w := by
          have h3 : (σ ^ (j:ℕ)) ((σ ^ ((i:ℕ) - (j:ℕ))) w) = (σ ^ (j:ℕ)) w := by
            rw [← LinearEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' (le_of_lt hgt), h1]
          exact (σ ^ (j:ℕ)).injective h3
        have h4 : ((LayersAlt.quotMulEquiv h ξ) ^ ((i:ℕ) - (j:ℕ))) (Additive.toMul w) =
            Additive.toMul w := by
          rw [hwrepr] at h2
          rw [hσpow] at h2
          rw [← hyy, LayersAlt.quotMulEquiv_pow_mk]
          exact Additive.ofMul.injective h2
        have hdiv0 : orderOf (LayersAlt.quotMulEquiv h ξ) ∣ (i:ℕ) - (j:ℕ) :=
          orderOf_dvd_iff_pow_eq_one.mpr (by
            by_contra hc
            exact hfpfσe _ hc _ hwne h4)
        have hdiv : 2 ^ N - 1 ∣ (i:ℕ) - (j:ℕ) := by rwa [hordσe] at hdiv0
        have hlt' : (i:ℕ) - (j:ℕ) < 2 ^ N - 1 := lt_of_le_of_lt (Nat.sub_le _ _) i.isLt
        rcases Nat.eq_zero_or_pos ((i:ℕ)-(j:ℕ)) with h0 | hpos
        · omega
        · exact absurd (Nat.le_of_dvd hpos hdiv) (not_le.mpr hlt')
    have horbcard : ((Finset.univ : Finset (Fin (2 ^ N - 1))).image
        (fun i : Fin (2 ^ N - 1) => (⟨(σ ^ (i : ℕ)) w, hpowU (i : ℕ)⟩ : ↥U))).card
        = 2 ^ N - 1 := by
      rw [Finset.card_image_of_injOn (fun i _ j _ h => hinj h), Finset.card_univ,
        Fintype.card_fin]
    have hsub : ((Finset.univ : Finset (Fin (2 ^ N - 1))).image
        (fun i : Fin (2 ^ N - 1) => (⟨(σ ^ (i : ℕ)) w, hpowU (i : ℕ)⟩ : ↥U)))
        ⊆ (Finset.univ : Finset ↥U).erase 0 := by
      intro z hz
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      rw [Finset.mem_image] at hz
      obtain ⟨i, _, hi⟩ := hz
      rw [← hi]
      intro hc
      have hc' : (σ ^ (i:ℕ)) w = 0 := by simpa using hc
      exact hw0 ((σ ^ (i:ℕ)).injective (by rw [map_zero]; exact hc'))
    have hcardErase : ((Finset.univ : Finset ↥U).erase (0:↥U)).card = 2 ^ N - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcardU']
    have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq (by rw [horbcard, hcardErase]))
    have hyorb : (⟨y, hyU⟩ : ↥U) ∈ (Finset.univ : Finset (Fin (2 ^ N - 1))).image
        (fun i : Fin (2 ^ N - 1) => (⟨(σ ^ (i : ℕ)) w, hpowU (i : ℕ)⟩ : ↥U)) := by
      rw [heq, Finset.mem_erase]
      exact ⟨by simpa using hy0, Finset.mem_univ _⟩
    rw [Finset.mem_image] at hyorb
    obtain ⟨i, _, hi⟩ := hyorb
    exact ⟨(i:ℕ), congrArg Subtype.val hi⟩
  -- ### conclusion
  have hw_not_fix : Ā w ≠ w := by
    intro hcon
    have : w ∈ W ⊓ U := by rw [Submodule.mem_inf, hWmem]; exact ⟨hcon, hwU⟩
    rw [hWU, Submodule.mem_bot] at this
    exact hw0 this
  obtain ⟨k, hk⟩ := htrans (Ā w) (hĀU w hwU)
    (fun h => hw0 (Ā.injective (by rw [h, map_zero])))
  have hmk : (QuotientGroup.mk (A yy) : P ⧸ Subgroup.center P) = QuotientGroup.mk ((ξ ^ k) yy) := by
    have h1 : Ā w = (σ ^ k) w := hk.symm
    rw [hwrepr, hĀmk, hσpow] at h1
    exact Additive.ofMul.injective h1
  have hmem : (A yy)⁻¹ * ((ξ ^ k) yy) ∈ Subgroup.center P := QuotientGroup.eq.mp hmk
  have hsqeq : (A yy) * (A yy) = ((ξ ^ k) yy) * ((ξ ^ k) yy) :=
    sq_eq_sq_of_mem_center_mul (hzsq := hzsq) hmem
  have hAy2 : (A yy) * (A yy) = yy * yy := by
    rw [← map_mul A yy yy, hAfix (yy * yy) (by simpa [pow_two] using hsq yy)]
  have hξ2 : ((ξ ^ k) yy) * ((ξ ^ k) yy) = (ξ ^ k) (yy * yy) := by rw [map_mul]
  have hfix : (ξ ^ k) (yy * yy) = yy * yy := by rw [hξ2.symm, ← hsqeq, hAy2]
  have hkne : ξ ^ k ≠ 1 := by
    intro hc
    apply hw_not_fix
    rw [← hk, (hσ_pow_eq_one k).mpr (by rw [quotMulEquiv_pow, hc, quotMulEquiv_one])]
    rfl
  have hy2 : yy * yy = 1 := hξ.fpf k hkne (yy * yy) hfix
  have hyZ : yy ∈ Subgroup.center P :=
    h.omega1_le_center (h.mem_omega1.mpr (by rw [pow_two]; exact hy2))
  have : QuotientGroup.mk yy = 1 := (QuotientGroup.eq_one_iff yy).mpr hyZ
  exact hw0 (by rw [hwrepr, this]; rfl)

end Work.PSU3.StageA
