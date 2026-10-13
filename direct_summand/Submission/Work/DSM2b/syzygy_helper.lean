import Mathlib
import Submission.Work.DSM2b.FlatSetup
import Submission.Work.DSM2b.assembly_aux

/-!
# The mod-`π ^ n` syzygy step

`Work.DSM2b.syzygy_mod_pow` (and its self-contained variant here) is the step

*if `B ⧸ π ^ n B` is flat over `R ⧸ π ^ n R` for all `n` and `g : R ^ k → R ^ m` satisfies the
elementwise Artin–Rees property with shift `c`, then any `y : B ^ k` with `coordBase g y` divisible
by `π ^ n` coordinatewise lies in the `B`-span of `ker g` modulo `π ^ (n - c)`:*

It is proved here by reducing to the quotient `M = B ⧸ π ^ n B` over `S = R ⧸ π ^ n R`: flatness of
`M` over `S` identifies the kernel of the base change `g ⊗ M` with the span of `ker g`, Artin–Rees
relates `ker (g mod π ^ n)` to `ker g`, and the two identifications are lifted back to `B`.
-/

namespace Work.DSM2b

universe u

open TensorProduct

section Abstract

variable {S M : Type u} [CommRing S] [CommRing M] [Algebra S M]

/-- `piScalarRight` carries the range of `S'.subtype.lTensor M` into `spanBase S'`. -/
lemma piScalarRight_mem_spanBase {k : ℕ} (S' : Submodule S (Fin k → S))
    {t : M ⊗[S] (Fin k → S)}
    (ht : t ∈ LinearMap.range (LinearMap.lTensor M S'.subtype)) :
    TensorProduct.piScalarRight S M M (Fin k) t ∈ spanBase (R := S) (B := M) S' := by
  obtain ⟨u, rfl⟩ := ht
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add]
      exact Submodule.add_mem _ hx hy
  | tmul m s =>
      rw [LinearMap.lTensor_tmul, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul]
      have hfun : (fun j => S'.subtype s j • m) =
          m • coeffMap (R := S) (B := M) (s : Fin k → S) := by
        ext j
        simp only [coeffMap_apply, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
        exact mul_comm _ _
      rw [hfun]
      exact Submodule.smul_mem _ m
        (Submodule.subset_span ⟨(s : Fin k → S), s.2, rfl⟩)

/-- **Flatness computes kernels.**  For `M` flat over `S` and a coordinate map
`g : S ^ k → S ^ m`, the kernel of the base change of `g` to `M` is the `M`-span of the image of
`ker g`. -/
lemma mem_spanBase_of_coordBase_eq_zero [Module.Flat S M] {k m : ℕ}
    (g : (Fin k → S) →ₗ[S] (Fin m → S)) {z : Fin k → M}
    (hz : coordBase (R := S) (B := M) g z = 0) :
    z ∈ spanBase (R := S) (B := M) (LinearMap.ker g) := by
  have hex := Module.Flat.lTensor_exact M (LinearMap.exact_subtype_ker_map g)
  have hker : LinearMap.ker (LinearMap.lTensor M g) =
      LinearMap.range (LinearMap.lTensor M (LinearMap.ker g).subtype) :=
    LinearMap.exact_iff.mp hex
  have hz0 : (TensorProduct.piScalarRight S M M (Fin k)).symm z ∈
      LinearMap.ker (LinearMap.lTensor M g) := by
    rw [LinearMap.mem_ker]
    refine (TensorProduct.piScalarRight S M M (Fin m)).injective ?_
    rw [map_zero, piScalarRight_lTensor_coordBase, LinearEquiv.apply_symm_apply]
    exact hz
  rw [hker] at hz0
  obtain ⟨u, hu⟩ := hz0
  have hzu : (TensorProduct.piScalarRight S M M (Fin k))
      ((LinearMap.lTensor M (LinearMap.ker g).subtype) u) = z := by
    rw [hu, LinearEquiv.apply_symm_apply]
  rw [← hzu]
  exact piScalarRight_mem_spanBase _ (LinearMap.mem_range.mpr ⟨u, rfl⟩)

end Abstract

section Tower

variable {R S M : Type u} [CommRing R] [CommRing S] [CommRing M]
variable [Algebra R S] [Algebra S M] [Algebra R M] [IsScalarTower R S M]

/-- Base change of coordinate maps is compatible with a tower of algebras. -/
lemma coordBase_tower {k m : ℕ} (g : (Fin k → R) →ₗ[R] (Fin m → R)) (y : Fin k → M) :
    coordBase (R := S) (B := M) (coordBase (R := R) (B := S) g) y =
      coordBase (R := R) (B := M) g y := by
  ext i
  rw [coordBase_apply, coordBase_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coordBase_single (R := R) (B := S) g j, coeffMap_apply,
    IsScalarTower.algebraMap_apply R S M ((g (Pi.single j 1)) i)]

/-- The same for the componentwise maps. -/
lemma coeffMap_tower {k : ℕ} (y : Fin k → R) :
    coeffMap (R := S) (B := M) (coeffMap (R := R) (B := S) y) =
      coeffMap (R := R) (B := M) y := by
  ext i
  rw [coeffMap_apply, coeffMap_apply, coeffMap_apply,
    IsScalarTower.algebraMap_apply R S M (y i)]

end Tower


/-- Every element of `(R ⧸ I) ^ k` is the componentwise image of an element of `R ^ k`. -/
lemma exists_coeffMap_eq (R : Type u) [CommRing R] (I : Ideal R) {k : ℕ}
    (s : Fin k → R ⧸ I) : ∃ x : Fin k → R, coeffMap (R := R) (B := R ⧸ I) x = s := by
  choose x hx using fun j => Ideal.Quotient.mk_surjective (s j)
  exact ⟨x, by
    funext j
    rw [coeffMap_apply, Ideal.Quotient.algebraMap_eq]
    exact hx j⟩

section Main

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- The `R`-action on coordinate modules is the action through `algebraMap`. -/
lemma algebraMap_smul_pi {M : Type u} [CommRing M] [Algebra R M] {k : ℕ} (c : R) (v : Fin k → M) :
    c • v = algebraMap R M c • v := by
  ext i
  simp only [Pi.smul_apply, Algebra.smul_def, smul_eq_mul]
  rw [Algebra.algebraMap_self, RingHom.id_apply]

/-- **The mod-`π ^ n` syzygy step** (self-contained variant of `Work.DSM2b.syzygy_mod_pow`). -/
theorem syzygy_mod_pow_helper (π : R) [IsNoetherianRing R]
    (hflat : ∀ n : ℕ, Module.Flat (R ⧸ Ideal.span {π ^ n})
      (B ⧸ (Ideal.span {π ^ n}).map (algebraMap R B)))
    {k m : ℕ} (g : (Fin k → R) →ₗ[R] (Fin m → R)) (c : ℕ)
    (hAR : ∀ n (x : Fin k → R), (∀ i, g x i ∈ Ideal.span {π} ^ n) →
      ∃ z : Fin k → R, x - π ^ (n - c) • z ∈ LinearMap.ker g)
    (n : ℕ) {y : Fin k → B}
    (hy : ∀ i, coordBase (R := R) (B := B) g y i ∈ Ideal.span {algebraMap R B π} ^ n) :
    ∃ w : Fin k → B, w ∈ spanBase (R := R) (B := B) (LinearMap.ker g) ∧
      ∀ i, (y - w) i ∈ Ideal.span {algebraMap R B π} ^ (n - c) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨0, Submodule.zero_mem _, fun i => by simp⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hIdeal : Ideal.span {algebraMap R B π} ^ (N + 1) =
      (Ideal.span {π ^ (N + 1)}).map (algebraMap R B) := by
    rw [Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow]
  set J : Ideal B := (Ideal.span {π ^ (N + 1)}).map (algebraMap R B) with hJ
  set S : Type u := R ⧸ Ideal.span {π ^ (N + 1)} with hS
  set M : Type u := B ⧸ J with hM
  have hflatM : Module.Flat S M := hflat (N + 1)
  -- (1) the base changed coordinate map kills `mk ∘ y`
  have hz : coordBase (R := S) (B := M) (coordBase (R := R) (B := S) g)
      (fun j => Ideal.Quotient.mk J (y j)) = 0 := by
    funext i
    rw [Pi.zero_apply, coordBase_apply]
    have hcoef : ∀ j : Fin k, algebraMap S M
        ((coordBase (R := R) (B := S) g (Pi.single j 1)) i) =
        Ideal.Quotient.mk J (algebraMap R B ((g (Pi.single j 1)) i)) := by
      intro j
      rw [coordBase_single (R := R) (B := S) g j, coeffMap_apply,
        ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply R S M,
        ← IsScalarTower.algebraMap_apply R B M]
    have hterm : ∀ j : Fin k,
        Ideal.Quotient.mk J (algebraMap R B ((g (Pi.single j 1)) i)) *
          Ideal.Quotient.mk J (y j) =
        Ideal.Quotient.mk J (algebraMap R B ((g (Pi.single j 1)) i) * y j) :=
      fun j => (map_mul _ _ _).symm
    simp only [hcoef, hterm, ← map_sum, ← coordBase_apply]
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hIdeal]
    exact hy i
  -- (2) flatness: the class of `y` lies in the `M`-span of `ker (coordBase g)`
  have hzspan : (fun j => Ideal.Quotient.mk J (y j)) ∈
      spanBase (R := S) (B := M) (LinearMap.ker (coordBase (R := R) (B := S) g)) :=
    mem_spanBase_of_coordBase_eq_zero _ hz
  -- (3) corrected elements lie in the image of the `B`-span of `ker g`
  have key : ∀ z ∈ spanBase (R := S) (B := M)
        (LinearMap.ker (coordBase (R := R) (B := S) g)),
      ∃ w ∈ spanBase (R := R) (B := B) (LinearMap.ker g),
        coeffMap (R := B) (B := M) w - z ∈
          (Ideal.span {algebraMap R M π}) ^ (N + 1 - c) • (⊤ : Submodule M (Fin k → M)) := by
    intro z hz
    rw [spanBase] at hz
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · rintro v ⟨s, hs, rfl⟩
      obtain ⟨x, hx⟩ := exists_coeffMap_eq R (Ideal.span {π ^ (N + 1)}) s
      have hs0 : coordBase (R := R) (B := S) g s = 0 := LinearMap.mem_ker.mp hs
      have hgx : ∀ i, g x i ∈ Ideal.span {π} ^ (N + 1) := by
        intro i
        have h0 : (coordBase (R := R) (B := S) g (coeffMap x)) i = 0 := by
          rw [hx]; exact congrFun hs0 i
        rw [coordBase_apply] at h0
        have hmat : algebraMap R S ((g x) i) =
            ∑ j, algebraMap R S ((g (Pi.single j 1)) i) *
              (coeffMap (R := R) (B := S) x) j := by
          rw [apply_eq_sum_single_fin (R := R) g x i, map_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [map_mul, coeffMap_apply]
        have h1 : algebraMap R S ((g x) i) = 0 := by rw [hmat]; exact h0
        rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at h1
        rwa [Ideal.span_singleton_pow]
      obtain ⟨z', hz'⟩ := hAR (N + 1) x hgx
      set w' : Fin k → R := x - π ^ (N + 1 - c) • z' with hw'def
      have hxw : x = π ^ (N + 1 - c) • z' + w' := by rw [hw'def]; abel
      refine ⟨coeffMap (R := R) (B := B) w', Submodule.subset_span ⟨w', hz', rfl⟩, ?_⟩
      have h1 : coeffMap (R := B) (B := M) (coeffMap (R := R) (B := B) w') =
          coeffMap (R := R) (B := M) w' := coeffMap_tower (R := R) (S := B) (M := M) w'
      have h2 : coeffMap (R := S) (B := M) s = coeffMap (R := R) (B := M) x := by
        rw [← hx]
        exact coeffMap_tower (R := R) (S := S) (M := M) x
      rw [h1, h2]
      have hm : algebraMap R M (π ^ (N + 1 - c)) ∈
          (Ideal.span {algebraMap R M π}) ^ (N + 1 - c) := by
        rw [map_pow, Ideal.span_singleton_pow]
        exact Ideal.subset_span (Set.mem_singleton _)
      have hgoal : coeffMap (R := R) (B := M) w' - coeffMap (R := R) (B := M) x =
          -(algebraMap R M (π ^ (N + 1 - c)) • coeffMap (R := R) (B := M) z') := by
        rw [hxw, map_add, map_smul]
        rw [show π ^ (N + 1 - c) • coeffMap (R := R) (B := M) z' =
            algebraMap R M (π ^ (N + 1 - c)) • coeffMap (R := R) (B := M) z' from
          algebraMap_smul_pi (R := R) (M := M) _ _]
        abel
      rw [hgoal]
      exact Submodule.neg_mem _ (Submodule.smul_mem_smul hm Submodule.mem_top)
    · refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [map_zero, zero_sub]
      exact Submodule.neg_mem _ (Submodule.zero_mem _)
    · intro a b _ _ ha hb
      obtain ⟨wa, hwa, hba⟩ := ha
      obtain ⟨wb, hwb, hbb⟩ := hb
      exact ⟨wa + wb, Submodule.add_mem _ hwa hwb, by
        rw [map_add, add_sub_add_comm]
        exact Submodule.add_mem _ hba hbb⟩
    · intro d a _ ha
      obtain ⟨w, hw, hbw⟩ := ha
      obtain ⟨d', rfl⟩ := Ideal.Quotient.mk_surjective d
      refine ⟨d' • w, Submodule.smul_mem _ _ hw, ?_⟩
      have h1 : coeffMap (R := B) (B := M) (d' • w) =
          Ideal.Quotient.mk J d' • coeffMap (R := B) (B := M) w := by
        rw [map_smul]
        rfl
      rw [h1, ← smul_sub]
      exact Submodule.smul_mem _ _ hbw
  -- (4) conclude
  obtain ⟨w, hw, herr⟩ := key _ hzspan
  refine ⟨w, hw, fun i => ?_⟩
  have hyz : coeffMap (R := B) (B := M) y = fun j => Ideal.Quotient.mk J (y j) := by
    funext i
    rw [coeffMap_apply]
    rfl
  have hv : coeffMap (R := B) (B := M) (y - w) ∈
      (Ideal.span {algebraMap R M π}) ^ (N + 1 - c) • (⊤ : Submodule M (Fin k → M)) := by
    have hsub : coeffMap (R := B) (B := M) (y - w) =
        -(coeffMap (R := B) (B := M) w - fun j => Ideal.Quotient.mk J (y j)) := by
      rw [map_sub, hyz]; abel
    rw [hsub]
    exact Submodule.neg_mem _ herr
  have hmem : Ideal.Quotient.mk J ((y - w) i) ∈
      ((Ideal.span {algebraMap R B π}) ^ (N + 1 - c)).map (Ideal.Quotient.mk J) := by
    have hle : (Ideal.span {algebraMap R M π}) ^ (N + 1 - c) •
          (⊤ : Submodule M (Fin k → M)) ≤
        Submodule.pi Set.univ (fun _ => (Ideal.span {algebraMap R M π}) ^ (N + 1 - c)) := by
      rw [Submodule.smul_le]
      intro a ha m _ j
      simpa using Ideal.mul_mem_right (m j) _ ha
    have hc := hle hv
    rw [Submodule.mem_pi] at hc
    have hci := hc i (Set.mem_univ i)
    rw [coeffMap_apply] at hci
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]
    exact hci
  obtain ⟨a, ha, haeq⟩ :=
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hmem
  have hker : (y - w) i - a ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, haeq, sub_self]
  rw [← hIdeal] at hker
  have hxsum : (y - w) i = a + ((y - w) i - a) := by abel
  rw [hxsum]
  exact Ideal.add_mem _ ha (Ideal.pow_le_pow_right (Nat.sub_le (N + 1) c) hker)

end Main

end Work.DSM2b
