import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.DualityDefs
import Submission.Work.ORHughesFree.NaturalExtension.DualityAPI
import Submission.Work.ORHughesFree.NaturalExtension.dimOf_comp_le
import Submission.Work.ORHughesFree.NaturalExtension.dimOf_rows_eq_rk

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix Work.ORHughesFree

variable {R : Type u} [Ring R] [VonNeumannRegularRing R]

/-- **A linear section of `φ` over a finitely generated submodule.**  For an `R`-linear map
`φ : R^n → R^m` and a finite family `v` in `R^n`, there is a linear map `τ : R^m → R^n` whose
range lies in `W := span (range v)` and which is a right inverse of `φ` on `φ(W)`.

Indeed, `W` is the range of an idempotent `e`, so `g := φ ∘ e` has range `φ(W)`, which is a
finitely generated submodule of `R^m`, hence the range of an idempotent `f` and hence a direct
summand of the free module `R^m`.  The surjection `g : R^n ↠ range f` splits; composing the
splitting with `e` lands in `W` and still inverts `φ` on `φ(W)`. -/
theorem exists_linearSection_map_span {R : Type u} [Ring R] [VonNeumannRegularRing R]
    {n m k : ℕ} (φ : (Fin n → R) →ₗ[R] (Fin m → R)) (v : Fin k → (Fin n → R)) :
    ∃ τ : (Fin m → R) →ₗ[R] (Fin n → R),
      LinearMap.range τ ≤ Submodule.span R (Set.range v) ∧
      ∀ y ∈ Submodule.map φ (Submodule.span R (Set.range v)), φ (τ y) = y := by
  classical
  obtain ⟨e, he, hre⟩ := Work.ORHughesFree.StarRegular.exists_idempotent_range_span_aux v
  obtain ⟨f, hf, hrf⟩ :=
    Work.ORHughesFree.StarRegular.exists_idempotent_range_span_aux (fun j => φ (v j))
  set g : (Fin n → R) →ₗ[R] (Fin m → R) := φ ∘ₗ e with hgdef
  -- The range of `g = φ ∘ e` is `φ (span (range v)) = span (range (φ ∘ v)) = range f`.
  have hgr : LinearMap.range g = LinearMap.range f := by
    rw [hgdef, LinearMap.range_comp e φ, hre, Submodule.map_span, hrf]
    congr 1
    ext y
    simp [Set.mem_image, Set.mem_range]
  -- A set-theoretic section of `g` on the standard basis of `R^m`.
  have hmem : ∀ i : Fin m, ∃ y : Fin n → R, g y = f (Pi.single i (1 : R)) := by
    intro i
    have h : f (Pi.single i (1 : R)) ∈ LinearMap.range f := LinearMap.mem_range_self f _
    rw [← hgr] at h
    exact h
  choose t ht using hmem
  let b : Module.Basis (Fin m) R (Fin m → R) := Pi.basisFun R (Fin m)
  let σ : (Fin m → R) →ₗ[R] (Fin n → R) := (b.constr ℕ) t
  have hσ : g ∘ₗ σ = f := by
    refine b.ext fun i => ?_
    show g (σ (b i)) = f (b i)
    rw [show σ (b i) = t i from Module.Basis.constr_basis b ℕ t i, ht i,
      show b i = Pi.single i (1 : R) from Pi.basisFun_apply R (Fin m) i]
  refine ⟨e ∘ₗ σ, ?_, ?_⟩
  · calc LinearMap.range (e ∘ₗ σ) = Submodule.map e (LinearMap.range σ) :=
        LinearMap.range_comp σ e
      _ ≤ Submodule.map e ⊤ := Submodule.map_mono le_top
      _ = LinearMap.range e := Submodule.map_top e
      _ = Submodule.span R (Set.range v) := hre
  · intro y hy
    have hyg : y ∈ LinearMap.range g := by
      rw [hgdef, LinearMap.range_comp, hre]
      exact hy
    have hyf : y ∈ LinearMap.range f := hgr ▸ hyg
    have hfix : f y = y := by
      obtain ⟨z, hz⟩ := hyf
      rw [← hz]
      change (f ∘ₗ f) z = f z
      rw [← Module.End.mul_eq_comp, hf]
    have hσy : g (σ y) = f y := by
      have h := LinearMap.congr_fun hσ y
      simpa only [LinearMap.comp_apply] using h
    calc φ ((e ∘ₗ σ) y) = φ (e (σ y)) := rfl
      _ = (φ ∘ₗ e) (σ y) := rfl
      _ = g (σ y) := rfl
      _ = f y := hσy
      _ = y := hfix

/-- The `rdim` of the span of a finite family of vectors is `dimOf` of that family.  Both are
the rank of the (matrix of the) idempotent endomorphism onto the span; the two sides are
`rdim_eq_rk_rows` and `dimOf_rows_eq_rk` applied to the matrix whose rows are the family. -/
theorem rdim_span_range (rk : SylvesterRank R) {n k : ℕ} (v : Fin k → (Fin n → R)) :
    rdim rk (Submodule.span R (Set.range v)) = dimOf rk v := by
  have h1 := rdim_eq_rk_rows rk (fun i : Fin k => fun j : Fin n => v i j)
  have h2 := dimOf_rows_eq_rk rk (fun i : Fin k => fun j : Fin n => v i j)
  simpa using h1.trans h2.symm

/-- **Suffices to bound `dimOf` on finitely generated submodules.**  If `dimOf rk v ≤ c` for
every finite family `v` with values in `V`, then `rdim rk V ≤ c`.  This is just the definition of
`rdim` as a supremum, together with `dimOf_rows_eq_rk`. -/
theorem rdim_le_of_forall_dimOf_le {R : Type u} [Ring R] [VonNeumannRegularRing R]
    (rk : SylvesterRank R) {n : ℕ} (V : Submodule R (Fin n → R)) (c : ℝ)
    (h : ∀ (k : ℕ) (v : Fin k → (Fin n → R)), (∀ i, v i ∈ V) → dimOf rk v ≤ c) :
    rdim rk V ≤ c := by
  unfold rdim
  refine csSup_le (rdim_nonempty rk V) ?_
  rintro x ⟨m, A, hA, rfl⟩
  have hb := h m (fun i => fun j => A i j) hA
  rwa [dimOf_rows_eq_rk] at hb

/-- **The finitely generated case.**  For an `R`-linear map `φ : R^n → R^m` and a finitely
generated submodule `W = span (range v) ≤ R^n`, the dimension of `W` is at most the dimension
of `φ(W)` plus that of `W ⊓ ker φ`.

Since `Y := φ(W)` is the image of the idempotent projection onto `W`, it is a direct summand
of `R^m`; the surjection `φ|_W : W ↠ Y` therefore splits, giving `τ : R^m → R^n` with
`range τ ≤ W` and `φ (τ y) = y` for `y ∈ Y`.  With `C := τ(Y) ≤ W` and `K := W ⊓ ker φ`
every `w ∈ W` is `τ (φ w) + (w - τ (φ w)) ∈ K ⊔ C`, so `W = K ⊔ C` and
`rdim W ≤ rdim K + rdim C`; finally `rdim C = rdim Y` because `τ` is injective on `Y` with
inverse `φ`. -/
theorem dimOf_le_map_add_inf_ker (rk : SylvesterRank R) {n m k : ℕ}
    (φ : (Fin n → R) →ₗ[R] (Fin m → R)) (v : Fin k → (Fin n → R)) :
    dimOf rk v ≤ rdim rk (Submodule.map φ (Submodule.span R (Set.range v)))
      + rdim rk (Submodule.span R (Set.range v) ⊓ LinearMap.ker φ) := by
  classical
  obtain ⟨τ, hτrange, hτsec⟩ := exists_linearSection_map_span φ v
  set W : Submodule R (Fin n → R) := Submodule.span R (Set.range v) with hW
  set Y : Submodule R (Fin m → R) := Submodule.map φ W with hY
  set C : Submodule R (Fin n → R) := Submodule.map τ Y with hC
  set K : Submodule R (Fin n → R) := W ⊓ LinearMap.ker φ with hK
  -- `Y = span (range (φ ∘ v))`
  have himg : φ '' Set.range v = Set.range (fun j => φ (v j)) := by
    ext x
    constructor
    · rintro ⟨b, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨v j, ⟨j, rfl⟩, rfl⟩
  have h1 : Submodule.map φ W = Submodule.span R (Set.range (fun j => φ (v j))) := by
    rw [hW, Submodule.map_span, himg]
  have hτsec' : ∀ y ∈ Y, φ (τ y) = y := fun y hy => hτsec y hy
  -- `C = span (range (τ ∘ φ ∘ v))`
  have hset : τ '' Set.range (fun j => φ (v j)) = Set.range (fun j => τ (φ (v j))) := by
    ext x
    constructor
    · rintro ⟨b, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨φ (v j), ⟨j, rfl⟩, rfl⟩
  have hCspan : C = Submodule.span R (Set.range (fun j => τ (φ (v j)))) := by
    rw [hC, hY, h1, Submodule.map_span, hset]
  -- `C ≤ W` and `K ≤ W`
  have hCW : C ≤ W := by
    rw [hC, hY]
    calc Submodule.map τ (Submodule.map φ W)
        ≤ Submodule.map τ (⊤ : Submodule R (Fin m → R)) := Submodule.map_mono le_top
      _ = LinearMap.range τ := Submodule.map_top τ
      _ ≤ W := hτrange
  have hKW : K ≤ W := inf_le_left
  -- `W = K ⊔ C`
  have hsup : W ≤ K ⊔ C := by
    intro w hw
    have hφw : φ w ∈ Y := ⟨w, hw, rfl⟩
    have hCmem : τ (φ w) ∈ C := ⟨φ w, hφw, rfl⟩
    have hKmem : w - τ (φ w) ∈ K := by
      rw [hK]
      refine Submodule.mem_inf.mpr ⟨W.sub_mem hw (hCW hCmem), ?_⟩
      rw [LinearMap.mem_ker, map_sub, hτsec' (φ w) hφw, sub_self]
    exact Submodule.mem_sup.mpr ⟨w - τ (φ w), hKmem, τ (φ w), hCmem, by abel⟩
  have hWK : W = K ⊔ C := le_antisymm hsup (sup_le hKW hCW)
  have hWle : rdim rk W ≤ rdim rk K + rdim rk C := by
    rw [hWK]
    exact rdim_sup_le rk K C
  -- `rdim C = rdim Y`
  have hdimτ : dimOf rk (fun j => τ (φ (v j))) = dimOf rk (fun j => φ (v j)) := by
    refine le_antisymm (dimOf_comp_le rk τ (fun j => φ (v j))) ?_
    have h' : (fun j : Fin k => φ (τ (φ (v j)))) = (fun j => φ (v j)) := by
      funext j
      exact hτsec' (φ (v j)) ⟨v j, Submodule.subset_span ⟨j, rfl⟩, rfl⟩
    calc dimOf rk (fun j => φ (v j)) = dimOf rk (fun j => φ (τ (φ (v j)))) := by rw [h']
      _ ≤ dimOf rk (fun j => τ (φ (v j))) :=
          dimOf_comp_le rk φ (fun j => τ (φ (v j)))
  calc dimOf rk v = rdim rk W := by rw [hW]; exact (rdim_span_range rk v).symm
    _ ≤ rdim rk K + rdim rk C := hWle
    _ = rdim rk K + dimOf rk (fun j => τ (φ (v j))) := by rw [hCspan, rdim_span_range]
    _ = rdim rk K + dimOf rk (fun j => φ (v j)) := by rw [hdimτ]
    _ = rdim rk K + rdim rk Y := by rw [hY, h1, rdim_span_range]
    _ = rdim rk Y + rdim rk K := add_comm _ _

/-- **Dimension additivity (rank–nullity) for `rdim`.**  For an `R`-linear map `φ : R^n → R^m` and
any left submodule `V ≤ R^n`, `rdim rk V ≤ rdim rk (V.map φ) + rdim rk (V ⊓ ker φ)`.

PROOF SKETCH.
(0) `rdim rk (span (range v)) = dimOf rk v` for every finite family `v` — this is
`(rdim_eq_rk_rows rk (fun i j => v i j)).trans (dimOf_rows_eq_rk rk …).symm`; call it
`rdim_span_range`.  Consequently `rdim rk V = sSup {dimOf rk v | v a finite family with values
in V}` (use the definition of `rdim` as a `csSup` and `rdim_span_range`), so it suffices to
bound `dimOf rk v ≤ rdim (V.map φ) + rdim (V ⊓ ker φ)` for every finite family `v` with values
in `V`; and by monotonicity (`rdim_mono`) it suffices to do the finitely generated case
`W := span (range v) ≤ V`.
(1) Let `W = span (range v)`.  `Y := φ(W) = span (range (φ ∘ v))` is a finitely generated
submodule of `R^m`, hence (von Neumann regular ring) a direct summand of `R^m`, hence
projective.  So the surjection `φ|_W : W ↠ Y` splits: there is a linear
`τ : (Fin m → R) →ₗ[R] (Fin n → R)` with `LinearMap.range τ ≤ W` and
`φ (τ y) = y` for all `y ∈ Y`.  (Build it exactly as in `dimOf_comp_le`'s proof: take an
idempotent `e` of `R^n` with `range e = W`, `Module.Projective.of_split` for
`range (φ ∘ e)`, `LinearMap.exists_rightInverse_of_surjective`, and precompose with the
projection.)
(2) With `C := τ(Y) ≤ W` and `K := W ⊓ ker φ`: every `w ∈ W` is
`τ (φ w) + (w - τ (φ w)) ∈ C ⊔ K`, so `W = K ⊔ C`; and `K ⊓ C = 0`
(if `τ y ∈ ker φ` then `y = φ (τ y) = 0`).  Hence
`rdim W ≤ rdim K + rdim C` (`rdim_sup_le` with `K ⊔ C = W`), and
`rdim C = rdim Y`: take a finite family `u` with `Y = span (range u)`; then
`C = span (range (τ ∘ u))`, and `dimOf (τ ∘ u) ≤ dimOf u` and `dimOf u ≤ dimOf (τ ∘ u)`
both follow from `dimOf_comp_le` applied to the global maps `τ` (its range lies in `W`, and
`τ (u j) = τ (φ (τ (u j)))`) and `φ` (`φ (τ (u j)) = u j`).
(3) Finish with `rdim_mono` (`K ≤ V ⊓ ker φ` and `W.map φ ≤ V.map φ`). -/
theorem rdimAdditivity {R : Type u} [Ring R] [VonNeumannRegularRing R]
    (rk : SylvesterRank R) {n m : ℕ} (φ : (Fin n → R) →ₗ[R] (Fin m → R))
    (V : Submodule R (Fin n → R)) :
    rdim rk V ≤ rdim rk (V.map φ) + rdim rk (V ⊓ LinearMap.ker φ) := by
  refine rdim_le_of_forall_dimOf_le rk V _ ?_
  intro k v hv
  refine le_trans (dimOf_le_map_add_inf_ker rk φ v) (add_le_add ?_ ?_)
  · exact rdim_mono rk (Submodule.map_mono (Submodule.span_le.mpr (Set.range_subset_iff.mpr hv)))
  · exact rdim_mono rk (inf_le_inf_right _ (Submodule.span_le.mpr (Set.range_subset_iff.mpr hv)))

end Work.ORHughesFree.NaturalExtension
