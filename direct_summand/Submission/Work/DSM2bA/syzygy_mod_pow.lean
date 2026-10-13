import Mathlib
import Submission.Work.DSM2b.FlatSetup

namespace Work.DSM2bA

universe u

open Work.DSM2b
open TensorProduct

/-! ## Auxiliary lemmas -/

/-- `algebraMap` from `R ⧸ I` to `B ⧸ I.map (algebraMap R B)`, on a class. -/
lemma algebraMap_quot_apply {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (I : Ideal R) (r : R) :
    algebraMap (R ⧸ I) (B ⧸ I.map (algebraMap R B)) (Ideal.Quotient.mk I r)
      = Ideal.Quotient.mk (I.map (algebraMap R B)) (algebraMap R B r) := by
  rw [show Ideal.Quotient.mk (I.map (algebraMap R B)) (algebraMap R B r)
        = algebraMap R (B ⧸ I.map (algebraMap R B)) r from rfl,
      IsScalarTower.algebraMap_apply R (R ⧸ I) (B ⧸ I.map (algebraMap R B)) r,
      Ideal.Quotient.algebraMap_eq I]

/-- Componentwise extension of scalars is compatible with a tower of algebras. -/
lemma coeffMap_coeffMap_tower {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra B C] [Algebra R C] [IsScalarTower R B C] {k : ℕ} (x : Fin k → R) :
    coeffMap (R := B) (B := C) (coeffMap (R := R) (B := B) x)
      = coeffMap (R := R) (B := C) x := by
  ext i
  simp only [coeffMap_apply]
  rw [IsScalarTower.algebraMap_apply R B C (x i)]

/-- `coordBase` is compatible with a tower of algebras. -/
lemma coordBase_coordBase_tower {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra B C] [Algebra R C] [IsScalarTower R B C] {k m : ℕ}
    (g : (Fin k → R) →ₗ[R] (Fin m → R)) (z : Fin k → C) :
    coordBase (R := B) (B := C) (coordBase (R := R) (B := B) g) z
      = coordBase (R := R) (B := C) g z := by
  ext i
  rw [coordBase_apply, coordBase_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (Pi.single j (1 : B)) = coeffMap (R := R) (B := B) (Pi.single j (1 : R)) by
        funext l
        rw [coeffMap_apply]
        by_cases h : l = j
        · subst h; simp
        · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero],
      coordBase_coeffMap (R := R) (B := B) g (Pi.single j (1 : R)), coeffMap_apply]
  rw [IsScalarTower.algebraMap_apply R B C ((g (Pi.single j (1 : R))) i)]

/-- The componentwise image of a `B`-multiple is the `B ⧸ I`-multiple of the image. -/
lemma quot_smul_quot {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (I : Ideal R) {k : ℕ} (b : B) (W : Fin k → B) :
    (Ideal.Quotient.mk (I.map (algebraMap R B)) b)
        • (fun i => Ideal.Quotient.mk (I.map (algebraMap R B)) (W i))
      = (fun i => Ideal.Quotient.mk (I.map (algebraMap R B)) ((b • W) i)) := by
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]

/-- The two module actions on `(B ⧸ I)^k` (`B ⧸ I` itself and `R ⧸ I`) commute. -/
lemma quot_smul_smul_comm {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (I : Ideal R) {k : ℕ} (b : B) (s : R ⧸ I) (v : Fin k → B ⧸ I.map (algebraMap R B)) :
    (Ideal.Quotient.mk (I.map (algebraMap R B)) b) • (s • v)
      = s • ((Ideal.Quotient.mk (I.map (algebraMap R B)) b) • v) := by
  ext i
  simp only [Pi.smul_apply]
  rw [smul_eq_mul, Algebra.smul_def, Algebra.smul_def]
  ring

/-! ### The flatness step -/

/-- The range of `(ker g).subtype.lTensor M`, transported back to `M^k`, lies in
`spanBase (ker g)`. -/
lemma piScalarRight_lTensor_subtype_mem_spanBase {S M : Type u} [CommRing S] [CommRing M]
    [Algebra S M] {k m : ℕ} (g : (Fin k → S) →ₗ[S] (Fin m → S))
    (t : M ⊗[S] (LinearMap.ker g)) :
    TensorProduct.piScalarRight S M M (Fin k) (LinearMap.lTensor M (LinearMap.ker g).subtype t)
      ∈ spanBase (R := S) (B := M) (LinearMap.ker g) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
  | tmul c s =>
      rw [LinearMap.lTensor_tmul, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul]
      change (fun j => (s : Fin k → S) j • c) ∈ spanBase (R := S) (B := M) (LinearMap.ker g)
      have hmem : coeffMap (R := S) (B := M) (s : Fin k → S)
          ∈ spanBase (R := S) (B := M) (LinearMap.ker g) :=
        Submodule.subset_span ⟨(s : Fin k → S), s.2, rfl⟩
      have h_eq : (fun j => (s : Fin k → S) j • c)
          = c • coeffMap (R := S) (B := M) (s : Fin k → S) := by
        ext j
        rw [Pi.smul_apply, coeffMap_apply, Algebra.smul_def, smul_eq_mul]
        ring
      rw [h_eq]
      exact Submodule.smul_mem _ c hmem

/-- If `M` is flat over `S` and `g : S^k → S^m` is linear, then the kernel of the base change
`coordBase g : M^k → M^m` is contained in the `M`-span of `ker g`. -/
lemma flat_ker_le_spanBase {S M : Type u} [CommRing S] [CommRing M] [Algebra S M]
    (hM : Module.Flat S M) {k m : ℕ} (g : (Fin k → S) →ₗ[S] (Fin m → S)) (z : Fin k → M)
    (hz : coordBase (R := S) (B := M) g z = 0) :
    z ∈ spanBase (R := S) (B := M) (LinearMap.ker g) := by
  have hlt : LinearMap.lTensor M g
      ((TensorProduct.piScalarRight S M M (Fin k)).symm z) = 0 := by
    apply (TensorProduct.piScalarRight S M M (Fin m)).injective
    rw [map_zero, piScalarRight_lTensor_coordBase, LinearEquiv.apply_symm_apply]
    exact hz
  have hex : LinearMap.ker (LinearMap.lTensor M g)
      = (LinearMap.lTensor M (LinearMap.ker g).subtype).range := by
    have h := Module.Flat.lTensor_exact M (LinearMap.exact_subtype_ker_map g)
    rwa [LinearMap.exact_iff] at h
  have hmem : (TensorProduct.piScalarRight S M M (Fin k)).symm z
      ∈ LinearMap.range (LinearMap.lTensor M (LinearMap.ker g).subtype) := by
    rw [← hex, LinearMap.mem_ker]
    exact hlt
  obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hmem
  have hz' : z = TensorProduct.piScalarRight S M M (Fin k)
      (LinearMap.lTensor M (LinearMap.ker g).subtype t) := by
    rw [ht, LinearEquiv.apply_symm_apply]
  rw [hz']
  exact piScalarRight_lTensor_subtype_mem_spanBase g t

/-! ### The Artin–Rees step -/

/-- Elementwise Artin–Rees, lifted to the quotient `R ⧸ π^n`: if `t : (R ⧸ π^n)^k` is killed by
the base change of `g` to `R ⧸ π^n`, then some `w ∈ ker g` satisfies
`t - coeffMap w ∈ (π)^(n-c) • ⊤`. -/
lemma ar_lift_coeffMap {R : Type u} [CommRing R] (π : R) {k m : ℕ}
    (g : (Fin k → R) →ₗ[R] (Fin m → R)) (c n : ℕ)
    (hAR : ∀ N (x : Fin k → R), (∀ i, g x i ∈ Ideal.span {π} ^ N) →
      ∃ z : Fin k → R, x - π ^ (N - c) • z ∈ LinearMap.ker g)
    {t : Fin k → R ⧸ Ideal.span {π ^ n}}
    (ht : coordBase (R := R) (B := R ⧸ Ideal.span {π ^ n}) g t = 0) :
    ∃ w : Fin k → R, w ∈ LinearMap.ker g ∧
      ∃ u : Fin k → R ⧸ Ideal.span {π ^ n},
        t = coeffMap (R := R) (B := R ⧸ Ideal.span {π ^ n}) w +
          (Ideal.Quotient.mk (Ideal.span {π ^ n}) π) ^ (n - c) • u := by
  obtain ⟨x, hx⟩ : ∃ x : Fin k → R,
      coeffMap (R := R) (B := R ⧸ Ideal.span {π ^ n}) x = t := by
    refine ⟨fun i => Classical.choose (Ideal.Quotient.mk_surjective (t i)), ?_⟩
    ext i
    rw [coeffMap_apply, Ideal.Quotient.algebraMap_eq]
    exact Classical.choose_spec (Ideal.Quotient.mk_surjective (t i))
  have hgx : ∀ i, g x i ∈ Ideal.span {π} ^ n := by
    intro i
    have h2 : coeffMap (R := R) (B := R ⧸ Ideal.span {π ^ n}) (g x) = 0 := by
      rw [← coordBase_coeffMap (R := R) (B := R ⧸ Ideal.span {π ^ n}) g x, hx, ht]
    have h3 : algebraMap R (R ⧸ Ideal.span {π ^ n}) (g x i) = 0 := by
      have := congrFun h2 i
      simpa using this
    rw [Ideal.span_singleton_pow]
    refine (Ideal.Quotient.eq_zero_iff_mem (I := Ideal.span {π ^ n})).mp ?_
    rw [← Ideal.Quotient.algebraMap_eq]
    exact h3
  obtain ⟨z, hz⟩ := hAR n x hgx
  refine ⟨x - π ^ (n - c) • z, hz,
    coeffMap (R := R) (B := R ⧸ Ideal.span {π ^ n}) z, ?_⟩
  have hcoe : (π ^ (n - c) : R) • coeffMap (R := R) (B := R ⧸ Ideal.span {π ^ n}) z
      = (Ideal.Quotient.mk (Ideal.span {π ^ n}) π) ^ (n - c)
          • coeffMap (R := R) (B := R ⧸ Ideal.span {π ^ n}) z := by
    rw [← IsScalarTower.algebraMap_smul (R ⧸ Ideal.span {π ^ n}) (π ^ (n - c)), map_pow,
      Ideal.Quotient.algebraMap_eq]
  rw [← hx, map_sub, map_smul, hcoe, sub_add_cancel]

/-! ## The theorem -/

/-- **Syzygies modulo `π ^ n`, with Artin–Rees loss.**

Let `R` be a commutative ring, `π ∈ R`, `B` an `R`-algebra, and `g : R ^ k → R ^ m` a linear map
between coordinate modules; let `c : ℕ` be a constant such that every `x : R ^ k` whose image `g x`
has all coordinates divisible by `π ^ n` satisfies `x - π ^ (n - c) • z ∈ ker g` for some `z`
(elementwise Artin–Rees).  Assume moreover that `B ⧸ π ^ n B` is flat over `R ⧸ π ^ n R` for every
`n`.

Then for `y : B ^ k` whose image under the base-changed map `Work.DSM2b.coordBase g` has all
coordinates divisible by `π ^ n`, the element `y` lies in the `B`-span of `ker g` (namely
`Work.DSM2b.spanBase (LinearMap.ker g)`) up to an error in `π ^ (n - c) B ^ k`.

Suggested route.  Put `S := R ⧸ π ^ n`, `M := B ⧸ (π^n) • B` and let `q : B →ₐ[R] M` be the
reduction; let `z : Fin k → M` be `fun j ↦ q (y j)` and
`gS := Work.DSM2b.coordBase (R := R) (B := S) g`.  By `Work.DSM2b.map_coordBase` the hypothesis
says exactly that `Work.DSM2b.coordBase (R := S) (B := M) gS z = 0`.  Since `M` is flat over `S`,
`Module.Flat.lTensor_exact` applied to `LinearMap.exact_subtype_ker_map gS` gives
`LinearMap.ker (gS.lTensor M) = LinearMap.range ((LinearMap.ker gS).subtype.lTensor M)`; translating
back with `Work.DSM2b.piScalarRight_lTensor_coordBase` gives
`z ∈ Work.DSM2b.spanBase (LinearMap.ker gS)`.  Finally `hAR` shows that `LinearMap.ker gS` is
contained in the image of `LinearMap.ker g + π ^ (n-c) • ⊤` in `S^k`, and lifting the resulting
relation along `q` gives that `y` differs from `Work.DSM2b.spanBase (LinearMap.ker g)` by an element
of `π ^ (n-c) B^k`. -/
theorem syzygy_mod_pow {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] (π : R) {k m : ℕ}
    (g : (Fin k → R) →ₗ[R] (Fin m → R)) (c : ℕ)
    (hAR : ∀ n (x : Fin k → R), (∀ i, g x i ∈ Ideal.span {π} ^ n) →
      ∃ z : Fin k → R, x - π ^ (n - c) • z ∈ LinearMap.ker g)
    (hflat : ∀ n : ℕ, Module.Flat (R ⧸ Ideal.span {π ^ n})
      (B ⧸ (Ideal.span {π ^ n}).map (algebraMap R B)))
    (n : ℕ) {y : Fin k → B}
    (hy : ∀ i, Work.DSM2b.coordBase g y i ∈ Ideal.span {algebraMap R B π} ^ n) :
    ∃ w : Fin k → B, w ∈ Work.DSM2b.spanBase (LinearMap.ker g) ∧
      ∀ i, (y - w) i ∈ Ideal.span {algebraMap R B π} ^ (n - c) := by
  set I : Ideal R := Ideal.span {π ^ n} with hIdef
  set J : Ideal B := I.map (algebraMap R B) with hJdef
  have hJspan : Ideal.span {algebraMap R B π} ^ n = J := by
    rw [hJdef, hIdef, Ideal.span_singleton_pow, ← map_pow, Ideal.map_span, Set.image_singleton]
  have hyJ : ∀ i, coordBase g y i ∈ J := fun i => hJspan ▸ hy i
  have hzR : coordBase (R := R) (B := B ⧸ J) g (fun j => Ideal.Quotient.mk J (y j)) = 0 := by
    have hmap := map_coordBase (R := R) (B := B) (C := B ⧸ J) (Ideal.Quotient.mkₐ R J) g y
    have hzeq : (fun j => Ideal.Quotient.mk J (y j))
        = (fun j => (Ideal.Quotient.mkₐ R J) (y j)) := by
      funext j; rw [Ideal.Quotient.mkₐ_eq_mk]
    rw [hzeq, ← hmap]
    ext i
    rw [Pi.zero_apply, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hyJ i)
  have hzS : coordBase (R := R ⧸ I) (B := B ⧸ J)
      (coordBase (R := R) (B := R ⧸ I) g) (fun j => Ideal.Quotient.mk J (y j)) = 0 := by
    rw [coordBase_coordBase_tower (R := R) (B := R ⧸ I) (C := B ⧸ J) g
      (fun j => Ideal.Quotient.mk J (y j))]
    exact hzR
  have hzmem : (fun j => Ideal.Quotient.mk J (y j))
      ∈ spanBase (R := R ⧸ I) (B := B ⧸ J)
          (LinearMap.ker (coordBase (R := R) (B := R ⧸ I) g)) :=
    flat_ker_le_spanBase (hM := hflat n) (g := coordBase (R := R) (B := R ⧸ I) g) _ hzS
  have hmain : ∃ W : Fin k → B, W ∈ spanBase (R := R) (B := B) (LinearMap.ker g) ∧
      ∃ v : Fin k → (B ⧸ J),
        (fun j => Ideal.Quotient.mk J (y j))
          = (fun i => Ideal.Quotient.mk J (W i))
            + (Ideal.Quotient.mk I π) ^ (n - c) • v := by
    have hmem : (fun j => Ideal.Quotient.mk J (y j))
        ∈ Submodule.span (B ⧸ J)
            (coeffMap (R := R ⧸ I) (B := B ⧸ J) ''
              (LinearMap.ker (coordBase (R := R) (B := R ⧸ I) g) : Set (Fin k → R ⧸ I))) :=
      hzmem
    refine Submodule.span_induction (p := fun x _ => ∃ W : Fin k → B,
        W ∈ spanBase (R := R) (B := B) (LinearMap.ker g) ∧
        ∃ v : Fin k → (B ⧸ J),
          x = (fun i => Ideal.Quotient.mk J (W i))
            + (Ideal.Quotient.mk I π) ^ (n - c) • v) ?_ ?_ ?_ ?_ hmem
    · rintro x ⟨t, ht, rfl⟩
      obtain ⟨w, hw, u, hu⟩ := ar_lift_coeffMap (π := π) (g := g) (c := c) (n := n) hAR
        (t := t) (LinearMap.mem_ker.mp ht)
      have hcw : coeffMap (R := R ⧸ I) (B := B ⧸ J) (coeffMap (R := R) (B := R ⧸ I) w)
          = (fun i => Ideal.Quotient.mk J ((coeffMap (R := R) (B := B) w) i)) := by
        ext i
        simp only [coeffMap_apply]
        rw [← IsScalarTower.algebraMap_apply R (R ⧸ I) (B ⧸ J) (w i)]
        rfl
      refine ⟨coeffMap (R := R) (B := B) w, Submodule.subset_span ⟨w, hw, rfl⟩,
        coeffMap (R := R ⧸ I) (B := B ⧸ J) u, ?_⟩
      rw [hu, map_add, map_smul, hcw]
    · refine ⟨0, Submodule.zero_mem _, 0, ?_⟩
      ext i
      simp
    · rintro x y _ _ ⟨W1, hW1, v1, hv1⟩ ⟨W2, hW2, v2, hv2⟩
      refine ⟨W1 + W2, Submodule.add_mem _ hW1 hW2, v1 + v2, ?_⟩
      rw [hv1, hv2]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [map_add, smul_add, Algebra.smul_def, Algebra.smul_def]
      ring
    · rintro a x _ ⟨W, hW, v, hv⟩
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
      refine ⟨b • W, Submodule.smul_mem _ b hW, (Ideal.Quotient.mk J b) • v, ?_⟩
      rw [hv, smul_add, quot_smul_quot I b W, quot_smul_smul_comm I b _ v]
  obtain ⟨W, hW, v, hv⟩ := hmain
  choose liftv hliftv using fun i => Ideal.Quotient.mk_surjective (v i)
  refine ⟨W, hW, fun i => ?_⟩
  have hsc : algebraMap (R ⧸ I) (B ⧸ J) ((Ideal.Quotient.mk I π) ^ (n - c))
      = Ideal.Quotient.mk J ((algebraMap R B π) ^ (n - c)) := by
    rw [map_pow, algebraMap_quot_apply I π, ← map_pow]
  have hq : Ideal.Quotient.mk J (y i)
      = Ideal.Quotient.mk J (W i + (algebraMap R B π) ^ (n - c) * liftv i) := by
    have h := congrFun hv i
    rw [Pi.add_apply, Pi.smul_apply, Algebra.smul_def, hsc, ← hliftv i, ← map_mul, ← map_add] at h
    exact h
  have h1 : y i - (W i + (algebraMap R B π) ^ (n - c) * liftv i)
      ∈ Ideal.span {algebraMap R B π} ^ (n - c) :=
    Ideal.pow_le_pow_right (Nat.sub_le n c)
      (hJspan.symm ▸ (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hq)
  have h2 : (algebraMap R B π) ^ (n - c) * liftv i
      ∈ Ideal.span {algebraMap R B π} ^ (n - c) :=
    Ideal.mul_mem_right (liftv i) _
      (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) (n - c))
  have hsplit : (y - W) i
      = (y i - (W i + (algebraMap R B π) ^ (n - c) * liftv i))
        + (algebraMap R B π) ^ (n - c) * liftv i := by
    rw [Pi.sub_apply]
    ring
  rw [hsplit]
  exact Ideal.add_mem _ h1 h2

end Work.DSM2bA
