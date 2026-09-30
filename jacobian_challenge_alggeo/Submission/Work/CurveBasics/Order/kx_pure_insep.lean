import Mathlib
import Submission.Work.CurveBasics.Order.PureConstantsAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Polynomial

open scoped IntermediateField.algebraAdjoinAdjoin

namespace Work.CurveBasics.Order

/-! ## Auxiliary lemmas -/

/-- If `s ^ q` (`q > 0`) is transcendental over `k`, then `s` is transcendental over any
finite extension `E` of `k`. -/
theorem transcendental_of_finite_of_pow {k F : Type*} [Field k] [Field F] [Algebra k F]
    (E : IntermediateField k F) [FiniteDimensional k ↥E] {s : F} {q : ℕ} (hq : 0 < q)
    (hs : Transcendental k (s ^ q)) : Transcendental ↥E s := by
  intro h
  haveI : Algebra.IsIntegral k ↥E := Algebra.IsIntegral.of_finite k ↥E
  have h1 : IsIntegral ↥E s := h.isIntegral
  have h2 : IsIntegral k s := isIntegral_trans (R := k) (A := ↥E) s h1
  exact hs (h2.pow q |>.isAlgebraic)

/-- `K[s]` is integrally closed in `K(s)`, for `s` transcendental over `K`. -/
theorem isIntegrallyClosedIn_adjoin_singleton {K F : Type*} [Field K] [Field F] [Algebra K F]
    (s : F) (hs : Transcendental K s) :
    IsIntegrallyClosedIn ↥(Algebra.adjoin K ({s} : Set F))
      ↥(IntermediateField.adjoin K ({s} : Set F)) := by
  haveI : IsIntegrallyClosed ↥(Algebra.adjoin K ({s} : Set F)) :=
    IsIntegrallyClosed.of_equiv (Polynomial.algEquivOfTranscendental K s hs).toRingEquiv
  exact (isIntegrallyClosed_iff_isIntegrallyClosedIn
    ↥(IntermediateField.adjoin K ({s} : Set F))).mp ‹IsIntegrallyClosed _›

/-- An element of `K(s)` integral over `K[s]` lies in `K[s]` (`s` transcendental over `K`). -/
theorem mem_adjoin_of_isIntegral {K F : Type*} [Field K] [Field F] [Algebra K F]
    (s : F) (hs : Transcendental K s) (z : F)
    (hzT : z ∈ IntermediateField.adjoin K ({s} : Set F))
    (hz : IsIntegral ↥(Algebra.adjoin K ({s} : Set F)) z) :
    z ∈ (Algebra.adjoin K ({s} : Set F) : Set F) := by
  haveI hIC := isIntegrallyClosedIn_adjoin_singleton s hs
  let ψ : ↥(IntermediateField.adjoin K ({s} : Set F))
      →ₐ[↥(Algebra.adjoin K ({s} : Set F))] F :=
    { toFun := fun y => (y : F)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hψ : Function.Injective ψ := fun a b hab => Subtype.ext hab
  have hzψ : IsIntegral ↥(Algebra.adjoin K ({s} : Set F)) (ψ ⟨z, hzT⟩) := by
    have : ψ ⟨z, hzT⟩ = z := rfl
    rwa [this]
  have hz' : IsIntegral ↥(Algebra.adjoin K ({s} : Set F))
      (⟨z, hzT⟩ : ↥(IntermediateField.adjoin K ({s} : Set F))) :=
    (isIntegral_algHom_iff ψ hψ).mp hzψ
  obtain ⟨y, hy⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := ↥(Algebra.adjoin K ({s} : Set F)))
    (A := ↥(IntermediateField.adjoin K ({s} : Set F)))).mp hz'
  have hyz : ((algebraMap ↥(Algebra.adjoin K ({s} : Set F))
      ↥(IntermediateField.adjoin K ({s} : Set F)) y :
      ↥(IntermediateField.adjoin K ({s} : Set F))) : F) = z := by rw [hy]
  rw [← hyz]
  simpa using y.2

/-! ## The main theorem -/

/-- **Finiteness transfer.** If the integral closure of `R` in `L` is contained in a finitely
generated `R`-submodule `N` of a bigger field `F ⊇ L`, then it is a finite `R`-module. -/
theorem module_finite_integralClosure_of_le_fg
    {R L F : Type*} [CommRing R] [IsNoetherianRing R] [Field L] [Algebra R L]
    [Field F] [Algebra R F] [Algebra L F] [IsScalarTower R L F]
    (N : Submodule R F) (hN : Module.Finite R N)
    (hle : ∀ y : L, IsIntegral R y → algebraMap L F y ∈ N) :
    Module.Finite R ↥(integralClosure R L) := by
  let g : L →ₐ[R] F := IsScalarTower.toAlgHom R L F
  let f : ↥(integralClosure R L) →ₗ[R] F :=
    g.toLinearMap.comp (Subalgebra.val (integralClosure R L)).toLinearMap
  have hf : ∀ x : ↥(integralClosure R L), f x = algebraMap L F (x : L) := fun _ => rfl
  have hinj : Function.Injective f := by
    intro a b hab
    rw [hf, hf] at hab
    exact Subtype.ext (FaithfulSMul.algebraMap_injective L F hab)
  have hrange_le : f.range ≤ N := by
    rintro _ ⟨x, rfl⟩
    rw [hf]
    exact hle (x : L) (IsIntegralClosure.isIntegral_iff.mpr ⟨x, rfl⟩)
  have hNfg : N.FG := by rwa [← Module.Finite.iff_fg]
  have hrangefg : f.range.FG := Submodule.FG.of_le hNfg hrange_le
  haveI : Module.Finite R ↥f.range := by rwa [Module.Finite.iff_fg]
  exact Module.Finite.equiv (LinearEquiv.ofInjective f hinj).symm

/-- **Nagata's N-2 property for `k[x]`, purely inseparable case.**

If `x` is transcendental over `k` and `L / k(x)` is a finite *purely inseparable* extension, then
the integral closure of `k[x] ≅ k[X]` in `L` is a finite `k[x]`-module.

This is the hard core of the Japanese property of `k[x]` (cf. Stacks 032O/032N); the separable
case is Mathlib's `IsIntegralClosure.finite`.

Proof.  `PureConstantsAux.exists_finite_pure_constants_fixed` produces a field `F ⊇ L`, an
element `s : F` and a finite subextension `E / k` of `F` such that `x ↦ s ^ q` and every element
of `L` lands in `E(s) = E[s][1/s]`.  The `k[x]`-submodule `M` of `F` spanned by the finitely
many products `e • s ^ j` (`e` ranging over a `k`-basis of `E`, `j < q`) is a subalgebra
containing `E` and `s`, hence contains `E[s]`; and it is a finitely generated `k[x]`-module since
`s ^ q = x`.  Since `E[s]` is a polynomial ring over the field `E`, it is integrally closed in
`E(s)`, so every element of `L` integral over `k[x]` already lies in `E[s] ⊆ M`.  The finiteness
transfer `module_finite_integralClosure_of_le_fg` finishes the proof. -/
theorem kx_pure_insep {k L : Type*} [Field k] [Field L] [Algebra k L]
    (x : L) (hx : Transcendental k x)
    [FiniteDimensional ↥(IntermediateField.adjoin k ({x} : Set L)) L]
    [IsPurelyInseparable ↥(IntermediateField.adjoin k ({x} : Set L)) L] :
    Module.Finite ↥(Algebra.adjoin k ({x} : Set L))
      ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set L)) L) := by
  classical
  obtain ⟨F, hFld, hkF, hLF, hSTkLF, q, s, E, hxs, hEfin, hmem⟩ :=
    exists_finite_pure_constants_fixed (k := k) x hx
  letI : Field F := hFld
  letI : Algebra k F := hkF
  letI : Algebra L F := hLF
  letI : IsScalarTower k L F := hSTkLF
  -- `q` is positive
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · exfalso
      have h1 : algebraMap L F x = 1 := by rw [hxs, hq, pow_zero]
      have h2 : x = 1 := (algebraMap L F).injective (by rw [h1, map_one])
      have h3 : IsAlgebraic k x := by
        rw [h2]
        exact (isIntegral_one (R := k) (B := L)).isAlgebraic
      exact hx h3
    · exact hq
  -- `A = k[x]`
  let A : Subalgebra k L := Algebra.adjoin k ({x} : Set L)
  haveI hNoethA : IsNoetherianRing ↥A :=
    isNoetherianRing_of_ringEquiv (Polynomial k)
      (Polynomial.algEquivOfTranscendental k x hx).toRingEquiv
  -- the subalgebra `Es = E[s]` and the subfield `Ts = E(s)` of `F`
  let Es : Subalgebra ↥E F := Algebra.adjoin ↥E ({s} : Set F)
  let Ts : IntermediateField ↥E F := IntermediateField.adjoin ↥E ({s} : Set F)
  have hstrans : Transcendental ↥E s := by
    refine transcendental_of_finite_of_pow E hqpos ?_
    rw [← hxs]
    intro h
    exact hx ((isAlgebraic_algebraMap_iff (algebraMap L F).injective).mp h)
  -- a `k`-basis of `E`
  set b := Module.finBasis k ↥E with hb
  have hrepr : ∀ u : ↥E, algebraMap ↥E F u = ∑ m, b.repr u m • (b m : F) := by
    intro u
    conv_lhs => rw [← b.sum_repr u]
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => by simp
  -- the generating set `T` and the `A`-submodule `M` it spans
  let T : Set F :=
    Set.range fun p : Fin (Module.finrank k ↥E) × Fin q => (b p.1 : F) * s ^ (p.2 : ℕ)
  let M : Submodule ↥A F := Submodule.span ↥A T
  have hTfin : T.Finite := Set.finite_range _
  have hMfin : Module.Finite ↥A M := Module.Finite.iff_fg.mpr (Submodule.fg_span hTfin)
  -- the algebra structure on `F` over `↥A`, evaluated on powers of `x`
  have hxpow : ∀ m : ℕ, algebraMap ↥A F
      ((⟨x, Algebra.self_mem_adjoin_singleton k x⟩ : ↥A) ^ m) = s ^ (q * m) := by
    intro m
    rw [map_pow, show algebraMap ↥A F (⟨x, Algebra.self_mem_adjoin_singleton k x⟩ : ↥A) = s ^ q
      from hxs, pow_mul]
  -- every `b l * s ^ j` lies in `M`
  have hgen : ∀ (l : Fin (Module.finrank k ↥E)) (j : ℕ), (b l : F) * s ^ j ∈ M := by
    intro l j
    have hred : (b l : F) * s ^ j
        = algebraMap ↥A F ((⟨x, Algebra.self_mem_adjoin_singleton k x⟩ : ↥A) ^ (j / q))
            * ((b l : F) * s ^ (j % q)) := by
      rw [hxpow]
      conv_lhs => rw [← Nat.div_add_mod j q, pow_add]
      ring
    rw [hred]
    have hmemT : (b l : F) * s ^ (j % q) ∈ T := by
      refine Set.mem_range.mpr ⟨(l, ⟨j % q, Nat.mod_lt j hqpos⟩), ?_⟩
      simp
    have h := M.smul_mem ((⟨x, Algebra.self_mem_adjoin_singleton k x⟩ : ↥A) ^ (j / q))
      (Submodule.subset_span hmemT)
    simpa [Algebra.smul_def] using h
  -- products of two generators
  have hmulT : ∀ (p p' : Fin (Module.finrank k ↥E) × Fin q),
      ((b p.1 : F) * s ^ (p.2 : ℕ)) * ((b p'.1 : F) * s ^ (p'.2 : ℕ)) ∈ M := by
    intro p p'
    have h1 : ((b p.1 : F) * s ^ (p.2 : ℕ)) * ((b p'.1 : F) * s ^ (p'.2 : ℕ))
        = algebraMap ↥E F ((b p.1) * (b p'.1)) * s ^ ((p.2 : ℕ) + (p'.2 : ℕ)) := by
      have hcoe : (algebraMap ↥E F ((b p.1) * (b p'.1)) : F)
          = (b p.1 : F) * (b p'.1 : F) :=
        map_mul (algebraMap ↥E F) (b p.1) (b p'.1)
      rw [mul_mul_mul_comm, ← hcoe, ← pow_add]
    rw [h1, hrepr ((b p.1) * (b p'.1)), Finset.sum_mul]
    refine M.sum_mem fun m _ => ?_
    have hsm : (b m : F) * s ^ ((p.2 : ℕ) + (p'.2 : ℕ)) ∈ M := hgen m _
    have h := M.smul_mem (algebraMap k ↥A (b.repr ((b p.1) * (b p'.1)) m)) hsm
    have h2 : (b.repr ((b p.1) * (b p'.1)) m • (b m : F)) * s ^ ((p.2 : ℕ) + (p'.2 : ℕ))
        = (algebraMap k ↥A (b.repr ((b p.1) * (b p'.1)) m))
            • ((b m : F) * s ^ ((p.2 : ℕ) + (p'.2 : ℕ))) := by
      rw [Algebra.smul_mul_assoc]
      exact (IsScalarTower.algebraMap_smul (↥A)
        (b.repr ((b p.1) * (b p'.1)) m) ((b m : F) * s ^ ((p.2 : ℕ) + (p'.2 : ℕ)))).symm
    rw [h2]
    exact h
  -- elements of `E` lie in `M`
  have hmemE : ∀ u : ↥E, algebraMap ↥E F u ∈ M := by
    intro u
    have hu : u ∈ Submodule.span k (Set.range ⇑b) := by rw [b.span_eq]; trivial
    induction hu using Submodule.span_induction with
    | mem w hw => obtain ⟨l, rfl⟩ := hw; simpa using hgen l 0
    | zero => simpa using M.zero_mem
    | add w z _ _ ihw ihz => rw [map_add]; exact M.add_mem ihw ihz
    | smul c w _ ih =>
        have h := M.smul_mem (algebraMap k ↥A c) ih
        simpa [map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply k ↥A F] using h
  -- `M` is closed under multiplication
  have hmulM : ∀ u ∈ M, ∀ v ∈ M, u * v ∈ M := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
        intro v hv
        induction hv using Submodule.span_induction with
        | mem v hv => obtain ⟨p, rfl⟩ := hu; obtain ⟨p', rfl⟩ := hv; exact hmulT p p'
        | zero => rw [mul_zero]; exact M.zero_mem
        | add v w _ _ ihv ihw => rw [mul_add]; exact M.add_mem ihv ihw
        | smul c v _ ih => rw [mul_smul_comm]; exact M.smul_mem c ih
    | zero => intro v _; rw [zero_mul]; exact M.zero_mem
    | add u v _ _ ihu ihv => intro w hw; rw [add_mul]; exact M.add_mem (ihu w hw) (ihv w hw)
    | smul c u _ ih => intro v hv; rw [Algebra.smul_mul_assoc]; exact M.smul_mem c (ih v hv)
  -- `s ∈ M`
  have hsM : s ∈ M := by
    have h1 : (1 : F) = ∑ m, b.repr (1 : ↥E) m • (b m : F) := by
      simpa using hrepr (1 : ↥E)
    have h2 : s = ∑ m, b.repr (1 : ↥E) m • ((b m : F) * s) := by
      conv_lhs => rw [← one_mul s]
      rw [h1, Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => by rw [Algebra.smul_mul_assoc]
    rw [h2]
    refine M.sum_mem fun m _ => ?_
    have hsm : (b m : F) * s ∈ M := by simpa using hgen m 1
    have h := M.smul_mem (algebraMap k ↥A (b.repr (1 : ↥E) m)) hsm
    simpa [Algebra.smul_def, IsScalarTower.algebraMap_apply k ↥A F] using h
  -- `Es ⊆ M`
  have hEs_le_M : ∀ z ∈ (Es : Set F), z ∈ M := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact hsM
    | algebraMap r => exact hmemE r
    | add x' y' _ _ ihx ihy => exact M.add_mem ihx ihy
    | mul x' y' _ _ ihx ihy => exact hmulM x' ihx y' ihy
  -- `A ⊆ Es`
  have hAleEs : ∀ a : ↥A, algebraMap ↥A F a ∈ (Es : Set F) := by
    have key : Algebra.adjoin k ({x} : Set L) ≤
        Subalgebra.comap (IsScalarTower.toAlgHom k L F) (Es.restrictScalars k) := by
      rw [Algebra.adjoin_le_iff]
      rintro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      show algebraMap L F x ∈ (Es : Set F)
      rw [hxs]
      exact Subalgebra.pow_mem Es (Algebra.subset_adjoin (Set.mem_singleton s)) q
    exact fun a => key a.2
  -- the integrality statement
  have hInt : ∀ y : L, IsIntegral ↥A y → algebraMap L F y ∈ M := by
    intro y hy
    have hyF : IsIntegral ↥A (algebraMap L F y) :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥A L F)
        (show Function.Injective (algebraMap L F) from (algebraMap L F).injective)).mpr hy
    let φ : ↥A →+* ↥Es :=
      { toFun := fun a => ⟨algebraMap ↥A F a, hAleEs a⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a a' => Subtype.ext (by simp)
        map_zero' := Subtype.ext (by simp)
        map_add' := fun a a' => Subtype.ext (by simp) }
    letI : Algebra ↥A ↥Es := φ.toAlgebra
    haveI hST : IsScalarTower ↥A ↥Es F := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hyEs : IsIntegral ↥Es (algebraMap L F y) := IsIntegral.tower_top hyF
    exact hEs_le_M _ (mem_adjoin_of_isIntegral s hstrans (algebraMap L F y) (hmem y) hyEs)
  show Module.Finite ↥A ↥(integralClosure ↥A L)
  exact module_finite_integralClosure_of_le_fg M hMfin hInt

end Work.CurveBasics.Order
