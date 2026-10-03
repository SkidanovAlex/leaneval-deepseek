import Mathlib
import Submission.Work.ORHughesFree.Section3.RowVanishesDefs
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.DivisionRank.regular_fgSubmodule_projection

/-!
# Invariance of a `K₀`-linear dimension function under isomorphism

Let `U` be a von Neumann regular ring and `d` a function assigning a real number to every
submodule of `U ^ n`, which vanishes on `⊥` (`h0`) and is additive for direct sums presented
through a linear equivalence `U ^ n × U ^ m ≃ U ^ (n + m)` (`hadd`).  Then `d` only depends on
the isomorphism class of a *finitely generated* submodule: if `P ≤ U ^ n` and `Q ≤ U ^ m` are
finitely generated and isomorphic, then `d n P = d m Q`.

The proof has three ingredients.

* `d_map_aut`: `d` is invariant under linear automorphisms of `U ^ n`.  This is `hadd` with
  `m = 0`, since `U ^ 0` is the zero module and `n + 0 = n` definitionally.
* `Work.ORHughesFree.DivisionRank.regular_fgSubmodule_projection`: a finitely generated
  submodule of `U ^ n` over a von Neumann regular ring is the range of an idempotent
  endomorphism, i.e. a direct summand.
* `exists_prodAutomorphism`: an isomorphism `φ : P ≃ₗ Q` between the ranges of idempotent
  endomorphisms `e` (of `U ^ n`) and `f` (of `U ^ m`) extends to an automorphism of
  `U ^ n × U ^ m` carrying `P × 0` onto `0 × Q`; explicitly
  `σ (x, y) = ((1 - e) x + φ⁻¹ (f y), φ (e x) + (1 - f) y)`.

Combining these with a fixed linear equivalence `U ^ n × U ^ m ≃ U ^ (n + m)`
(`prodFinLinearEquiv`), the two applications of `hadd` (for `P × ⊥` and for `⊥ × Q`) and the
automorphism invariance applied to the middle term give the result.
-/

namespace Work.ORHughesFree.Section3

universe u

section Aux

variable {U : Type u} [Ring U]

/-- The canonical linear equivalence `U ^ n × U ^ m ≃ U ^ (n + m)` (concatenation of
coordinates). -/
noncomputable def prodFinLinearEquiv (n m : ℕ) :
    ((Fin n → U) × (Fin m → U)) ≃ₗ[U] (Fin (n + m) → U) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) U U).symm.trans
    ((LinearEquiv.piCongrLeft U (fun _ : Fin n ⊕ Fin m => U) finSumFinEquiv.symm).symm)

/-- A `K₀`-linear invariant of submodules of the free modules `U ^ n` is invariant under linear
automorphisms of `U ^ n`.

The automorphism is encoded as a linear equivalence `U ^ n × U ^ 0 ≃ U ^ (n + 0) = U ^ n`
sending `(x, 0)` to `σ x`, and `hadd` is applied with `m = 0`. -/
theorem d_map_aut (d : ∀ n : ℕ, Submodule U (Fin n → U) → ℝ)
    (h0 : ∀ n, d n ⊥ = 0)
    (hadd : ∀ (n m : ℕ) (e : ((Fin n → U) × (Fin m → U)) ≃ₗ[U] (Fin (n + m) → U))
      (P : Submodule U (Fin n → U)) (Q : Submodule U (Fin m → U)),
      d (n + m) (Submodule.map (e : ((Fin n → U) × (Fin m → U)) →ₗ[U] (Fin (n + m) → U))
          (Submodule.prod P Q))
        = d n P + d m Q)
    (n : ℕ) (σ : (Fin n → U) ≃ₗ[U] (Fin n → U)) (P : Submodule U (Fin n → U)) :
    d n (Submodule.map (σ : (Fin n → U) →ₗ[U] (Fin n → U)) P) = d n P := by
  let g : (Fin n → U) →ₗ[U] ((Fin n → U) × (Fin 0 → U)) :=
    (LinearMap.inl U (Fin n → U) (Fin 0 → U)).comp σ.symm.toLinearMap
  let f : ((Fin n → U) × (Fin 0 → U)) →ₗ[U] (Fin n → U) :=
    σ.toLinearMap.comp (LinearMap.fst U (Fin n → U) (Fin 0 → U))
  have h1 : f.comp g = LinearMap.id := by
    apply LinearMap.ext
    intro x
    show σ (σ.symm x) = x
    exact LinearEquiv.apply_symm_apply σ x
  have h2 : g.comp f = LinearMap.id := by
    apply LinearMap.ext
    intro p
    have hy : p.2 = 0 := Subsingleton.elim _ _
    show (σ.symm (σ p.1), 0) = p
    rw [LinearEquiv.symm_apply_apply σ p.1]
    exact Prod.ext rfl hy.symm
  let e : ((Fin n → U) × (Fin 0 → U)) ≃ₗ[U] (Fin n → U) := LinearEquiv.ofLinearMap f g h1 h2
  have h := hadd n 0 e P ⊥
  have hzero : d 0 (⊥ : Submodule U (Fin 0 → U)) = 0 := h0 0
  have hh : d n (Submodule.map (e : ((Fin n → U) × (Fin 0 → U)) →ₗ[U] (Fin n → U))
      (Submodule.prod P ⊥)) = d n P + d 0 (⊥ : Submodule U (Fin 0 → U)) := h
  have hfst : Submodule.map (LinearMap.fst U (Fin n → U) (Fin 0 → U))
      (Submodule.prod P ⊥) = P := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (Submodule.mem_prod.mp hp).1
    · intro hx
      exact ⟨(x, 0), Submodule.mem_prod.mpr ⟨hx, Submodule.zero_mem _⟩, rfl⟩
  have hmap : Submodule.map (e : ((Fin n → U) × (Fin 0 → U)) →ₗ[U] (Fin n → U))
      (Submodule.prod P ⊥) = Submodule.map (σ : (Fin n → U) →ₗ[U] (Fin n → U)) P := by
    show Submodule.map (f : ((Fin n → U) × (Fin 0 → U)) →ₗ[U] (Fin n → U))
        (Submodule.prod P ⊥) = _
    rw [show (f : ((Fin n → U) × (Fin 0 → U)) →ₗ[U] (Fin n → U))
        = σ.toLinearMap.comp (LinearMap.fst U (Fin n → U) (Fin 0 → U)) from rfl,
      Submodule.map_comp, hfst]
  have h1' : d n (Submodule.map (e : ((Fin n → U) × (Fin 0 → U)) →ₗ[U] (Fin n → U))
      (Submodule.prod P ⊥)) = d n P := by linarith [hh, hzero]
  simpa [hmap] using h1'

/-- Let `e` be an idempotent endomorphism of `U ^ n` with range `P` and `f` an idempotent
endomorphism of `U ^ m` with range `Q`.  Then an isomorphism `φ : P ≃ₗ Q` induces an
automorphism of `U ^ n × U ^ m` mapping `P × 0` onto `0 × Q`, namely
`σ (x, y) = ((1 - e) x + φ⁻¹ (f y), (1 - f) y + φ (e x))`. -/
theorem exists_prodAutomorphism {n m : ℕ} {P : Submodule U (Fin n → U)}
    {Q : Submodule U (Fin m → U)}
    {e : (Fin n → U) →ₗ[U] (Fin n → U)} {f : (Fin m → U) →ₗ[U] (Fin m → U)}
    (he : e.comp e = e) (hre : LinearMap.range e = P)
    (hf : f.comp f = f) (hrf : LinearMap.range f = Q)
    (φ : P ≃ₗ[U] Q) :
    ∃ σ : ((Fin n → U) × (Fin m → U)) ≃ₗ[U] ((Fin n → U) × (Fin m → U)),
      Submodule.map (σ : ((Fin n → U) × (Fin m → U)) →ₗ[U] ((Fin n → U) × (Fin m → U)))
        (Submodule.prod P ⊥) = Submodule.prod ⊥ Q := by
  -- `e` fixes `P` and `f` fixes `Q`
  have he_id : ∀ x : Fin n → U, x ∈ P → e x = x := by
    intro x hx
    have hx' : x ∈ LinearMap.range e := hre ▸ hx
    obtain ⟨y, hy⟩ := hx'
    rw [← hy, ← LinearMap.comp_apply, he]
  have hf_id : ∀ y : Fin m → U, y ∈ Q → f y = y := by
    intro y hy
    have hy' : y ∈ LinearMap.range f := hrf ▸ hy
    obtain ⟨z, hz⟩ := hy'
    rw [← hz, ← LinearMap.comp_apply, hf]
  let e' : (Fin n → U) →ₗ[U] (Fin n → U) := LinearMap.id - e
  let f' : (Fin m → U) →ₗ[U] (Fin m → U) := LinearMap.id - f
  have he'_apply : ∀ x : Fin n → U, e' x = x - e x := by
    intro x
    rw [show e' = LinearMap.id - e from rfl, LinearMap.sub_apply, LinearMap.id_apply]
  have hf'_apply : ∀ y : Fin m → U, f' y = y - f y := by
    intro y
    rw [show f' = LinearMap.id - f from rfl, LinearMap.sub_apply, LinearMap.id_apply]
  let eP : (Fin n → U) →ₗ[U] P :=
    e.codRestrict P (fun x => by rw [← hre]; exact LinearMap.mem_range_self e x)
  let fQ : (Fin m → U) →ₗ[U] Q :=
    f.codRestrict Q (fun y => by rw [← hrf]; exact LinearMap.mem_range_self f y)
  let A : ((Fin n → U) × (Fin m → U)) →ₗ[U] (Fin n → U) :=
    (e'.comp (LinearMap.fst U (Fin n → U) (Fin m → U)))
      + (P.subtype.comp ((φ.symm : Q →ₗ[U] P).comp
          (fQ.comp (LinearMap.snd U (Fin n → U) (Fin m → U)))))
  let B : ((Fin n → U) × (Fin m → U)) →ₗ[U] (Fin m → U) :=
    (f'.comp (LinearMap.snd U (Fin n → U) (Fin m → U)))
      + (Q.subtype.comp ((φ : P →ₗ[U] Q).comp
          (eP.comp (LinearMap.fst U (Fin n → U) (Fin m → U)))))
  let σ : ((Fin n → U) × (Fin m → U)) →ₗ[U] ((Fin n → U) × (Fin m → U)) := A.prod B
  have hσ_apply : ∀ p : (Fin n → U) × (Fin m → U),
      σ p = (e' p.1 + ((φ.symm (fQ p.2) : P) : Fin n → U),
             f' p.2 + ((φ (eP p.1) : Q) : Fin m → U)) := by
    intro p
    exact Prod.ext rfl rfl
  have he0 : ∀ x : Fin n → U, x ∈ P → e' x = 0 := by
    intro x hx
    rw [he'_apply x, he_id x hx, sub_self]
  have hf0 : ∀ y : Fin m → U, y ∈ Q → f' y = 0 := by
    intro y hy
    rw [hf'_apply y, hf_id y hy, sub_self]
  have he1 : ∀ x : Fin n → U, e' (e' x) = e' x := by
    intro x
    rw [he'_apply, he'_apply, map_sub, ← LinearMap.comp_apply, he]
    abel
  have hf1 : ∀ y : Fin m → U, f' (f' y) = f' y := by
    intro y
    rw [hf'_apply, hf'_apply, map_sub, ← LinearMap.comp_apply, hf]
    abel
  have hfQ_zero : ∀ y : Fin m → U, fQ (f' y) = 0 := by
    intro y
    apply Subtype.ext
    show f (f' y) = (0 : Fin m → U)
    rw [hf'_apply y, map_sub, ← LinearMap.comp_apply, hf, sub_self]
  have heP_zero : ∀ x : Fin n → U, eP (e' x) = 0 := by
    intro x
    apply Subtype.ext
    show e (e' x) = (0 : Fin n → U)
    rw [he'_apply x, map_sub, ← LinearMap.comp_apply, he, sub_self]
  -- `σ` is an involution
  have hσinv : ∀ p : (Fin n → U) × (Fin m → U), σ (σ p) = p := by
    intro p
    have hqP : ((φ.symm (fQ p.2) : P) : Fin n → U) ∈ P := (φ.symm (fQ p.2)).2
    have hpQ : ((φ (eP p.1) : Q) : Fin m → U) ∈ Q := (φ (eP p.1)).2
    have heq : e ((φ.symm (fQ p.2) : P) : Fin n → U) = ((φ.symm (fQ p.2) : P) : Fin n → U) :=
      he_id _ hqP
    have hfp : f ((φ (eP p.1) : Q) : Fin m → U) = ((φ (eP p.1) : Q) : Fin m → U) :=
      hf_id _ hpQ
    have hfQp' : fQ ((φ (eP p.1) : Q) : Fin m → U) = φ (eP p.1) := by
      apply Subtype.ext
      change f ((φ (eP p.1) : Q) : Fin m → U) = ((φ (eP p.1) : Q) : Fin m → U)
      rw [hfp]
    have hePq : eP ((φ.symm (fQ p.2) : P) : Fin n → U) = φ.symm (fQ p.2) := by
      apply Subtype.ext
      change e ((φ.symm (fQ p.2) : P) : Fin n → U) = ((φ.symm (fQ p.2) : P) : Fin n → U)
      rw [heq]
    have hfq : fQ (f' p.2 + ((φ (eP p.1) : Q) : Fin m → U)) = φ (eP p.1) := by
      rw [map_add, hfQ_zero p.2, hfQp', zero_add]
    have heq' : eP (e' p.1 + ((φ.symm (fQ p.2) : P) : Fin n → U)) = φ.symm (fQ p.2) := by
      rw [map_add, heP_zero p.1, hePq, zero_add]
    have he'' : e' (e' p.1 + ((φ.symm (fQ p.2) : P) : Fin n → U)) = e' p.1 := by
      rw [map_add, he1 p.1, he0 _ hqP, add_zero]
    have hf'' : f' (f' p.2 + ((φ (eP p.1) : Q) : Fin m → U)) = f' p.2 := by
      rw [map_add, hf1 p.2, hf0 _ hpQ, add_zero]
    have hfQy : ((fQ p.2 : Q) : Fin m → U) = f p.2 := rfl
    have hePx : ((eP p.1 : P) : Fin n → U) = e p.1 := rfl
    rw [hσ_apply p, hσ_apply (e' p.1 + ((φ.symm (fQ p.2) : P) : Fin n → U),
      f' p.2 + ((φ (eP p.1) : Q) : Fin m → U))]
    simp only
    refine Prod.ext ?_ ?_
    · simp only
      rw [he'', hfq, LinearEquiv.symm_apply_apply, hePx, he'_apply p.1]
      abel
    · simp only
      rw [hf'', heq', LinearEquiv.apply_symm_apply, hfQy, hf'_apply p.2]
      abel
  refine ⟨LinearEquiv.mk σ (⇑σ) hσinv hσinv, ?_⟩
  apply le_antisymm
  · rintro z ⟨w, hw, rfl⟩
    have hw' := Submodule.mem_prod.mp hw
    have hy : w.2 = 0 := (Submodule.mem_bot U).mp hw'.2
    rw [hσ_apply, hy]
    refine Submodule.mem_prod.mpr ⟨?_, ?_⟩
    · have hfq0 : fQ (0 : Fin m → U) = 0 := Subtype.ext (by simp [fQ])
      rw [he0 w.1 hw'.1, hfq0, map_zero, zero_add]
      exact Submodule.zero_mem (⊥ : Submodule U (Fin n → U))
    · have h0f : f' (0 : Fin m → U) = 0 := hf0 0 (Submodule.zero_mem _)
      have hex : eP w.1 = ⟨w.1, hw'.1⟩ := Subtype.ext (he_id w.1 hw'.1)
      rw [h0f, zero_add, hex]
      exact (φ ⟨w.1, hw'.1⟩).2
  · intro z hz
    have hz' := Submodule.mem_prod.mp hz
    have hz1 : z.1 = 0 := (Submodule.mem_bot U).mp hz'.1
    have hxP : ((φ.symm ⟨z.2, hz'.2⟩ : P) : Fin n → U) ∈ P := (φ.symm ⟨z.2, hz'.2⟩).2
    refine ⟨(((φ.symm ⟨z.2, hz'.2⟩ : P) : Fin n → U), (0 : Fin m → U)),
      Submodule.mem_prod.mpr ⟨hxP, Submodule.zero_mem _⟩, ?_⟩
    rw [hσ_apply]
    refine Prod.ext ?_ ?_
    · have hfq0 : fQ (0 : Fin m → U) = 0 := Subtype.ext (by simp [fQ])
      rw [he0 _ hxP, hfq0, map_zero, zero_add]
      exact hz1.symm
    · have h0f : f' (0 : Fin m → U) = 0 := hf0 0 (Submodule.zero_mem _)
      have hex : eP ((φ.symm ⟨z.2, hz'.2⟩ : P) : Fin n → U) = φ.symm ⟨z.2, hz'.2⟩ := by
        apply Subtype.ext
        change e ((φ.symm ⟨z.2, hz'.2⟩ : P) : Fin n → U)
          = ((φ.symm ⟨z.2, hz'.2⟩ : P) : Fin n → U)
        rw [he_id _ hxP]
      rw [h0f, zero_add, hex, LinearEquiv.apply_symm_apply]

end Aux

theorem vnIsoInvariance {U : Type u} [Ring U] [Work.ORHughesFree.VonNeumannRegularRing U]
    (d : ∀ n : ℕ, Submodule U (Fin n → U) → ℝ)
    (h0 : ∀ n, d n ⊥ = 0)
    (hadd : ∀ (n m : ℕ) (e : ((Fin n → U) × (Fin m → U)) ≃ₗ[U] (Fin (n + m) → U))
      (P : Submodule U (Fin n → U)) (Q : Submodule U (Fin m → U)),
      d (n + m) (Submodule.map (e : ((Fin n → U) × (Fin m → U)) →ₗ[U] (Fin (n + m) → U))
          (Submodule.prod P Q))
        = d n P + d m Q)
    {n m : ℕ} {P : Submodule U (Fin n → U)} {Q : Submodule U (Fin m → U)}
    (hP : P.FG) (hQ : Q.FG) (φ : P ≃ₗ[U] Q) : d n P = d m Q := by
  obtain ⟨e, he, hre⟩ := Work.ORHughesFree.DivisionRank.regular_fgSubmodule_projection n P hP
  obtain ⟨f, hf, hrf⟩ := Work.ORHughesFree.DivisionRank.regular_fgSubmodule_projection m Q hQ
  obtain ⟨σ, hσ⟩ := exists_prodAutomorphism he hre hf hrf φ
  set e₀ : ((Fin n → U) × (Fin m → U)) ≃ₗ[U] (Fin (n + m) → U) := prodFinLinearEquiv n m
  set σ₀ : (Fin (n + m) → U) ≃ₗ[U] (Fin (n + m) → U) := (e₀.symm.trans σ).trans e₀
  have haut := d_map_aut d h0 hadd (n + m) σ₀
    (Submodule.map (e₀ : ((Fin n → U) × (Fin m → U)) →ₗ[U] (Fin (n + m) → U))
      (Submodule.prod P ⊥))
  have hcomp : (σ₀ : (Fin (n + m) → U) →ₗ[U] (Fin (n + m) → U)).comp
        (e₀ : ((Fin n → U) × (Fin m → U)) →ₗ[U] (Fin (n + m) → U))
      = (e₀ : ((Fin n → U) × (Fin m → U)) →ₗ[U] (Fin (n + m) → U)).comp
        (σ : ((Fin n → U) × (Fin m → U)) →ₗ[U] ((Fin n → U) × (Fin m → U))) := by
    apply LinearMap.ext
    intro z
    show σ₀ (e₀ z) = e₀ (σ z)
    rw [show σ₀ = (e₀.symm.trans σ).trans e₀ from rfl]
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  have hmap : Submodule.map (σ₀ : (Fin (n + m) → U) →ₗ[U] (Fin (n + m) → U))
        (Submodule.map (e₀ : ((Fin n → U) × (Fin m → U)) →ₗ[U] (Fin (n + m) → U))
          (Submodule.prod P ⊥))
      = Submodule.map (e₀ : ((Fin n → U) × (Fin m → U)) →ₗ[U] (Fin (n + m) → U))
        (Submodule.prod ⊥ Q) := by
    rw [← Submodule.map_comp, hcomp, Submodule.map_comp, hσ]
  calc d n P = d n P + d m ⊥ := by linarith [h0 m]
    _ = d (n + m) (Submodule.map (e₀ : ((Fin n → U) × (Fin m → U)) →ₗ[U] (Fin (n + m) → U))
          (Submodule.prod P ⊥)) := (hadd n m e₀ P ⊥).symm
    _ = d (n + m) (Submodule.map (σ₀ : (Fin (n + m) → U) →ₗ[U] (Fin (n + m) → U))
          (Submodule.map (e₀ : ((Fin n → U) × (Fin m → U)) →ₗ[U] (Fin (n + m) → U))
            (Submodule.prod P ⊥))) := haut.symm
    _ = d (n + m) (Submodule.map (e₀ : ((Fin n → U) × (Fin m → U)) →ₗ[U] (Fin (n + m) → U))
          (Submodule.prod ⊥ Q)) := by rw [hmap]
    _ = d n ⊥ + d m Q := hadd n m e₀ ⊥ Q
    _ = d m Q := by linarith [h0 n]

end Work.ORHughesFree.Section3
