import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Any two non-identity involutions of `Aut((ℤ/2)³) = GL(3,2)` are conjugate

`V = Multiplicative (Fin 3 → ZMod 2)` is the elementary abelian group `(ℤ/2)³`; its
automorphism group is `GL(3,2)`.  The aim of this file is

`Work.Hering.HardCore.aut_involutions_conj`:
every two elements `g h` of `Aut(V)` with `g ≠ 1`, `g² = 1`, `h ≠ 1`, `h² = 1` are conjugate.

The proof is the classical Jordan-type classification of involutions of `GL(n,2)`:
over `𝔽₂` an involution `g ≠ 1` of `GL(W)` with `finrank W ≤ 3` is a transvection
`x ↦ x + f x • v` (`hfv : f v = 0`), and any two non-zero transvections of `GL(W)` are
conjugate.  Both statements are proved here from scratch for `W` an arbitrary
finite-dimensional `𝔽₂`-space, and are then transported across the group isomorphism
`Aut(W) ≃* GL(W)` for `W = (ℤ/2)³`.

The results are stated for a general finite-dimensional `𝔽₂`-space because that is the
natural setting; for `W` of dimension `4` and higher the first statement is false (an
involution with two Jordan blocks of size `2` is not a transvection), which is exactly
why the dimension bound `≤ 3` appears.
-/

set_option autoImplicit false

namespace Work.Hering.HardCore

/-! ## Elementary facts about `𝔽₂` -/

theorem zmod_two_eq_zero_or_one_expTwo (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

theorem zmod_two_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  rcases zmod_two_eq_zero_or_one_expTwo a with h0 | h1
  · exact absurd h0 h
  · exact h1

/-- In a module over `𝔽₂`, `x + x = 0`. -/
theorem add_self_eq_zero_zmod2 {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (x : W) :
    x + x = 0 := by
  have h : ((1 : ZMod 2) + 1) • x = x + x := by rw [add_smul, one_smul]
  rw [← h]
  have h0 : ((1 : ZMod 2) + 1) = 0 := by decide
  rw [h0, zero_smul]

/-- A nonzero linear form on a module over `𝔽₂` takes the value `1` somewhere. -/
theorem exists_eq_one_of_ne_zero {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {f : Module.Dual (ZMod 2) W} (hf : f ≠ 0) : ∃ a : W, f a = 1 := by
  by_contra h
  have h' : ∀ a : W, f a = 0 := by
    intro a
    rcases zmod_two_eq_zero_or_one_expTwo (f a) with h0 | h1
    · exact h0
    · exact (h ⟨a, h1⟩).elim
  exact hf (LinearMap.ext h')

/-! ## A linear equivalence moving a nonzero vector to another -/

/-- Any nonzero vector of an `𝔽₂`-space can be moved to any other nonzero vector by a linear
equivalence (a transvection, when the two vectors are distinct). -/
theorem exists_linearEquiv_apply_eq_expTwo {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z]
    {x y : Z} (hx : x ≠ 0) (hy : y ≠ 0) : ∃ e : Z ≃ₗ[ZMod 2] Z, e x = y := by
  by_cases h : y = x
  · exact ⟨1, by simp [h]⟩
  · have hws : y ∉ Submodule.span (ZMod 2) ({x} : Set Z) := by
      intro hmem
      rcases Submodule.mem_span_singleton.mp hmem with ⟨c, hc⟩
      rcases zmod_two_eq_zero_or_one_expTwo c with rfl | rfl
      · rw [zero_smul] at hc; exact hy hc.symm
      · rw [one_smul] at hc; exact h hc.symm
    let φ₀ : Submodule.span (ZMod 2) ({x} : Set Z) →ₗ[ZMod 2] ZMod 2 :=
      LinearEquiv.coord (ZMod 2) Z x hx
    obtain ⟨φ, hφ, hφy⟩ := LinearMap.exists_extend_of_notMem φ₀ hws (1 : ZMod 2)
    have hφx : φ x = 1 := by
      have h1 := DFunLike.congr_fun hφ ⟨x, Submodule.mem_span_singleton_self x⟩
      simpa [φ₀, LinearEquiv.coord_self] using h1
    have huv : φ (y - x) = 0 := by rw [map_sub, hφx, hφy, sub_self]
    refine ⟨LinearEquiv.transvection huv, ?_⟩
    rw [LinearEquiv.transvection.apply huv, hφx, one_smul]
    abel

/-- Any nonzero vector of an `𝔽₂`-space can be moved to any nonzero vector of a space of the
same dimension by a linear equivalence. -/
theorem exists_linearEquiv_apply_eq_of_finrank_eq {Z Z' : Type*}
    [AddCommGroup Z] [Module (ZMod 2) Z] [AddCommGroup Z'] [Module (ZMod 2) Z']
    [Module.Finite (ZMod 2) Z] [Module.Finite (ZMod 2) Z']
    (hdim : Module.finrank (ZMod 2) Z = Module.finrank (ZMod 2) Z')
    {x : Z} {y : Z'} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ e : Z ≃ₗ[ZMod 2] Z', e x = y := by
  let γ : Z ≃ₗ[ZMod 2] Z' := LinearEquiv.ofFinrankEq Z Z' hdim
  have hγx : γ x ≠ 0 := fun h0 => hx (γ.injective (by rw [h0, map_zero]))
  obtain ⟨e', he'⟩ := exists_linearEquiv_apply_eq_expTwo hγx hy
  exact ⟨γ.trans e', by rw [LinearEquiv.trans_apply, he']⟩

/-! ## Non-identity involutions of `GL(≤3,2)` are transvections -/

/-- Over `𝔽₂`, an involution `g ≠ 1` of `GL(W)` with `finrank W ≤ 3` is a transvection
`x ↦ x + f x • v`.  The rank argument: `N = g - 1` satisfies `N² = 0`, so
`im N ⊆ ker N`, hence `2 · rank N ≤ finrank W ≤ 3` and `rank N = 1` (as `g ≠ 1`). -/
theorem isTransvection_of_involution {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] (hV : Module.finrank (ZMod 2) W ≤ 3)
    (g : W ≃ₗ[ZMod 2] W) (hg : g ≠ 1) (hg2 : g * g = 1) :
    ∃ (f : Module.Dual (ZMod 2) W) (v : W) (hfv : f v = 0),
      f ≠ 0 ∧ v ≠ 0 ∧ g = LinearEquiv.transvection hfv := by
  set N : W →ₗ[ZMod 2] W := (g : W →ₗ[ZMod 2] W) - 1 with hN
  have hgg : ∀ x, g (g x) = x := by
    intro x
    have h := congrArg (fun e : W ≃ₗ[ZMod 2] W => e x) hg2
    simpa using h
  -- `N` is nilpotent of index `2`
  have hN2 : ∀ x, N (N x) = 0 := by
    intro x
    have h1 : N x = g x - x := by simp [hN]
    have h2 : N (N x) = g (N x) - N x := by simp [hN]
    rw [h2, h1, map_sub, hgg x]
    have : x - g x - (g x - x) = (x - g x) + (x - g x) := by abel
    rw [this, add_self_eq_zero_zmod2]
  -- `N ≠ 0`
  have hNne : N ≠ 0 := by
    intro h0
    apply hg
    apply LinearEquiv.ext
    intro x
    have hx : N x = 0 := by rw [h0]; rfl
    have hxx : (g : W →ₗ[ZMod 2] W) x - x = 0 := by simpa [hN] using hx
    simpa using sub_eq_zero.mp hxx
  -- `rank N ≤ 1`
  have hle : Module.finrank (ZMod 2) (LinearMap.range N) ≤ 1 := by
    have hker : LinearMap.range N ≤ LinearMap.ker N := by
      rintro y ⟨x, rfl⟩
      exact LinearMap.mem_ker.mpr (hN2 x)
    have hfin : Module.finrank (ZMod 2) (LinearMap.range N)
        ≤ Module.finrank (ZMod 2) (LinearMap.ker N) := Submodule.finrank_mono hker
    have hrn := LinearMap.finrank_range_add_finrank_ker N
    omega
  have hge : 1 ≤ Module.finrank (ZMod 2) (LinearMap.range N) := by
    have hne : LinearMap.range N ≠ ⊥ := fun h0 => hNne (LinearMap.range_eq_bot.mp h0)
    exact Submodule.one_le_finrank_iff.mpr hne
  have hrank : Module.finrank (ZMod 2) (LinearMap.range N) = 1 := le_antisymm hle hge
  -- `g` is a dilatransvection
  have hdil : g ∈ LinearEquiv.dilatransvections (ZMod 2) W := by
    rw [LinearEquiv.mem_dilatransvections_iff_finrank]
    have h : ((g : W →ₗ[ZMod 2] W) - LinearMap.id) = N := rfl
    rw [h]
    exact hrank.le
  obtain ⟨f, v, hfv_eq⟩ := hdil
  have hg_eq : (g : W →ₗ[ZMod 2] W) = LinearMap.transvection f v := hfv_eq
  -- a bijective transvection has `f v = 0`
  have hfv : f v = 0 := by
    by_contra hne
    have hf1 : f v = 1 := zmod_two_eq_one_of_ne_zero hne
    have hv0 : v ≠ 0 := fun h0 => hne (by rw [h0, map_zero])
    have heq : g v = g 0 := by
      have h1 : g v = (LinearMap.transvection f v) v :=
        congrArg (fun L : W →ₗ[ZMod 2] W => L v) hg_eq
      have h2 : g 0 = (LinearMap.transvection f v) 0 :=
        congrArg (fun L : W →ₗ[ZMod 2] W => L 0) hg_eq
      rw [h1, h2, LinearMap.transvection.apply, LinearMap.transvection.apply, map_zero,
        zero_smul, add_zero, hf1, one_smul]
      exact add_self_eq_zero_zmod2 v
    exact hv0 (g.injective heq)
  refine ⟨f, v, hfv, ?_, ?_, ?_⟩
  · -- `f ≠ 0`
    intro hf0
    apply hg
    apply LinearEquiv.ext
    intro x
    have h1 : g x = (LinearMap.transvection f v) x :=
      congrArg (fun L : W →ₗ[ZMod 2] W => L x) hg_eq
    rw [h1, LinearMap.transvection.apply]
    simp [hf0]
  · -- `v ≠ 0`
    intro hv0
    apply hg
    apply LinearEquiv.ext
    intro x
    have h1 : g x = (LinearMap.transvection f v) x :=
      congrArg (fun L : W →ₗ[ZMod 2] W => L x) hg_eq
    rw [h1, LinearMap.transvection.apply, hv0, smul_zero, add_zero]
    simp
  · -- `g = transvection hfv`
    apply LinearEquiv.ext
    intro x
    have h1 : g x = (LinearMap.transvection f v) x :=
      congrArg (fun L : W →ₗ[ZMod 2] W => L x) hg_eq
    rw [LinearEquiv.transvection.coe_apply, h1]

/-! ## Any two nonzero transvections are conjugate -/

/-- **Flag-transitivity.**  If `f v = f' v' = 0` with `f, f', v, v' ≠ 0` then there is a linear
equivalence `u` with `u v = v'` and `f' ∘ u = f`.  Such a `u` maps the "flag"
`⟨v⟩ ⊆ ker f` to `⟨v'⟩ ⊆ ker f'`. -/
theorem exists_linearEquiv_maps_flag {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W]
    {f f' : Module.Dual (ZMod 2) W} {v v' : W} (hfv : f v = 0) (hf'v' : f' v' = 0)
    (hf : f ≠ 0) (hf' : f' ≠ 0) (hv : v ≠ 0) (hv' : v' ≠ 0) :
    ∃ u : W ≃ₗ[ZMod 2] W, u v = v' ∧ ∀ x : W, f' (u x) = f x := by
  obtain ⟨a, ha⟩ := exists_eq_one_of_ne_zero hf
  obtain ⟨a', ha'⟩ := exists_eq_one_of_ne_zero hf'
  -- a linear equivalence `ker f → ker f'` sending `v` to `v'`
  have hdim : Module.finrank (ZMod 2) (LinearMap.ker f)
      = Module.finrank (ZMod 2) (LinearMap.ker f') := by
    have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    have h2 := Module.Dual.finrank_ker_add_one_of_ne_zero hf'
    omega
  obtain ⟨ψ, hψ⟩ := exists_linearEquiv_apply_eq_of_finrank_eq hdim
    (x := (⟨v, hfv⟩ : LinearMap.ker f)) (y := (⟨v', hf'v'⟩ : LinearMap.ker f'))
    (fun h0 => hv (by simpa using congrArg Subtype.val h0))
    (fun h0 => hv' (by simpa using congrArg Subtype.val h0))
  -- extend it to `W` and correct the `f'`-component
  obtain ⟨ψe, hψe⟩ := LinearMap.exists_extend
    ((LinearMap.ker f').subtype.comp (ψ : LinearMap.ker f →ₗ[ZMod 2] LinearMap.ker f'))
  have hψe_apply : ∀ x : LinearMap.ker f, ψe (x : W) = (ψ x : W) := by
    intro x
    have h := DFunLike.congr_fun hψe x
    simpa using h
  set g : Module.Dual (ZMod 2) W := f - f'.comp ψe with hg_def
  set L : W →ₗ[ZMod 2] W := ψe + g.smulRight a' with hL_def
  have hLx : ∀ x : W, L x = ψe x + (f x - f' (ψe x)) • a' := by
    intro x
    simp only [hL_def, hg_def, LinearMap.add_apply, LinearMap.smulRight_apply,
      LinearMap.sub_apply, LinearMap.comp_apply]
  have hf'L : ∀ x : W, f' (L x) = f x := by
    intro x
    rw [hLx x, map_add, map_smul, ha', smul_eq_mul, mul_one]
    abel
  have hLzero : ∀ x : W, L x = 0 → x = 0 := by
    intro x hx0
    have hfx : f x = 0 := by
      have h := hf'L x
      rw [hx0, map_zero] at h
      exact h.symm
    have hψx : f' (ψe x) = 0 := by
      rw [hψe_apply ⟨x, hfx⟩]
      exact (ψ ⟨x, hfx⟩).2
    have hL0 : ψe x = 0 := by
      have h := hLx x
      rw [hx0, hfx, hψx, sub_zero, zero_smul, add_zero] at h
      exact h.symm
    have hψv : ψ ⟨x, hfx⟩ = 0 := by
      have h := hψe_apply ⟨x, hfx⟩
      rw [hL0] at h
      exact Subtype.ext (by simpa using h.symm)
    have : (⟨x, hfx⟩ : LinearMap.ker f) = 0 := ψ.injective (by rw [hψv, map_zero])
    simpa using Subtype.ext_iff.mp this
  have hinj : Function.Injective L := fun x y hxy =>
    sub_eq_zero.mp (hLzero (x - y) (by rw [map_sub, hxy, sub_self]))
  refine ⟨LinearEquiv.ofInjectiveEndo L hinj, ?_, ?_⟩
  · -- `u v = v'`
    show L v = v'
    rw [hLx v, hfv]
    have hψev : ψe v = v' := by
      rw [hψe_apply ⟨v, hfv⟩, hψ]
    rw [hψev, hf'v', sub_zero, zero_smul, add_zero]
  · -- `f' ∘ u = f`
    intro x
    show f' (L x) = f x
    exact hf'L x

/-- **Conjugacy of nonzero transvections.** -/
theorem transvection_conj {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W]
    {f f' : Module.Dual (ZMod 2) W} {v v' : W} (hfv : f v = 0) (hf'v' : f' v' = 0)
    (hf : f ≠ 0) (hf' : f' ≠ 0) (hv : v ≠ 0) (hv' : v' ≠ 0) :
    ∃ u : W ≃ₗ[ZMod 2] W,
      LinearEquiv.transvection hf'v' = u * LinearEquiv.transvection hfv * u⁻¹ := by
  obtain ⟨u, huv, hfu⟩ := exists_linearEquiv_maps_flag hfv hf'v' hf hf' hv hv'
  refine ⟨u, ?_⟩
  apply LinearEquiv.ext
  intro x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
    LinearEquiv.transvection.apply hfv, LinearEquiv.transvection.apply hf'v',
    map_add, map_smul, huv, u.apply_symm_apply]
  have hthis : f (u.symm x) = f' x := by
    have h := hfu (u.symm x)
    rw [u.apply_symm_apply] at h
    exact h.symm
  rw [hthis]

/-! ## Transport between `Aut(W)` and `GL(W)` -/

/-- The group isomorphism `Aut(W) ≃* GL(W)` for `W` an additive group (over `𝔽₂` on the right
hand side).  A multiplicative automorphism of `Multiplicative W` is additive, hence
`𝔽₂`-linear. -/
noncomputable def mulAutToLinEquiv {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] :
    MulAut (Multiplicative V) ≃* (V ≃ₗ[ZMod 2] V) where
  toFun g :=
    { toFun := fun v => (g (Multiplicative.ofAdd v)).toAdd
      invFun := fun v => (g.symm (Multiplicative.ofAdd v)).toAdd
      left_inv := by
        intro v
        show (g.symm (Multiplicative.ofAdd (g (Multiplicative.ofAdd v)).toAdd)).toAdd = v
        rw [ofAdd_toAdd, MulEquiv.symm_apply_apply]
        rfl
      right_inv := by
        intro v
        show (g (Multiplicative.ofAdd (g.symm (Multiplicative.ofAdd v)).toAdd)).toAdd = v
        rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]
        rfl
      map_add' := by
        intro v w
        show (g (Multiplicative.ofAdd (v + w))).toAdd
          = (g (Multiplicative.ofAdd v)).toAdd + (g (Multiplicative.ofAdd w)).toAdd
        rw [ofAdd_add, map_mul, toAdd_mul]
      map_smul' := by
        intro c v
        rcases zmod_two_eq_zero_or_one_expTwo c with rfl | rfl
        · show (g (Multiplicative.ofAdd ((0 : ZMod 2) • v))).toAdd
            = (0 : ZMod 2) • (g (Multiplicative.ofAdd v)).toAdd
          simp
        · show (g (Multiplicative.ofAdd ((1 : ZMod 2) • v))).toAdd
            = (1 : ZMod 2) • (g (Multiplicative.ofAdd v)).toAdd
          simp }
  invFun e :=
    { toFun := fun x => Multiplicative.ofAdd (e x.toAdd)
      invFun := fun x => Multiplicative.ofAdd (e.symm x.toAdd)
      left_inv := by intro x; simp
      right_inv := by intro x; simp
      map_mul' := by
        intro x y
        show Multiplicative.ofAdd (e (x * y).toAdd)
          = Multiplicative.ofAdd (e x.toAdd) * Multiplicative.ofAdd (e y.toAdd)
        rw [toAdd_mul, map_add, ofAdd_add] }
  left_inv := by
    intro g
    apply MulEquiv.ext
    intro x
    show Multiplicative.ofAdd ((g (Multiplicative.ofAdd x.toAdd)).toAdd) = g x
    rw [ofAdd_toAdd]
    rfl
  right_inv := by
    intro e
    apply LinearEquiv.ext
    intro v
    show e (Multiplicative.ofAdd v).toAdd = e v
    rw [toAdd_ofAdd]
  map_mul' := by
    intro g h
    apply LinearEquiv.ext
    intro v
    show ((g * h) (Multiplicative.ofAdd v)).toAdd
      = (g (Multiplicative.ofAdd (h (Multiplicative.ofAdd v)).toAdd)).toAdd
    rfl

/-! ## The main statement -/

theorem aut_involutions_conj (g h : MulAut (Multiplicative (Fin 3 → ZMod 2)))
    (hg : g ≠ 1) (hg2 : g * g = 1) (hh : h ≠ 1) (hh2 : h * h = 1) :
    ∃ u : MulAut (Multiplicative (Fin 3 → ZMod 2)), h = u * g * u⁻¹ := by
  have hV : Module.finrank (ZMod 2) (Fin 3 → ZMod 2) ≤ 3 := by
    simp
  let Φ : MulAut (Multiplicative (Fin 3 → ZMod 2))
      ≃* ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) := mulAutToLinEquiv
  have hg' : Φ g ≠ 1 := fun h1 => hg (Φ.injective (by rw [h1, map_one]))
  have hg2' : Φ g * Φ g = 1 := by rw [← map_mul, hg2, map_one]
  have hh' : Φ h ≠ 1 := fun h1 => hh (Φ.injective (by rw [h1, map_one]))
  have hh2' : Φ h * Φ h = 1 := by rw [← map_mul, hh2, map_one]
  obtain ⟨f, v, hfv, hf, hv, hg_eq⟩ :=
    isTransvection_of_involution hV (Φ g) hg' hg2'
  obtain ⟨f', v', hf'v', hf', hv', hh_eq⟩ :=
    isTransvection_of_involution hV (Φ h) hh' hh2'
  obtain ⟨U, hU⟩ := transvection_conj hfv hf'v' hf hf' hv hv'
  refine ⟨Φ.symm U, ?_⟩
  apply Φ.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hg_eq, hh_eq]
  exact hU

end Work.Hering.HardCore
