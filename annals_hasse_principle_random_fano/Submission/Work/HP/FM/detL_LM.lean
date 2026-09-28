import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Lat.detLAux
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.GM.detL_index

/-!
# The covolume of `LM c = Λ_c^{(sqN c)}` is `‖c‖²`

For a *primitive* integer vector `c : ι → ℤ`, the lattice

  `LM c = latMod c (sqN c) = {y : (sqN c : ℤ) ∣ ⟨y, c⟩}`

(where `sqN c = ∑ i, (c i)²` is the square of the Euclidean norm of `c`) has covolume
`detL (LM c) = sqN c = ‖c‖²`.

The proof is the classical "covolume = index" argument, in two steps.

* `detL_eq_natCard_quot`: if `L ⊆ ℤ^ι` carries a `ℤ`-basis indexed by `ι` (i.e. has full rank),
  then `detL L = [ℤ^ι : L] = Nat.card (ℤ^ι ⧸ L)`.  Indeed the Gram matrix of the basis `bL` of `L`
  in the standard orthonormal basis `Pi.basisFun ℤ ι` of `ℤ^ι` is the matrix `Tᵀ T`, where `T` is
  the coordinate matrix of `bL` in the standard basis; hence `det Gram = (det T)²` and therefore
  `detL L = |det T|`; the latter is the index by `Submodule.natAbs_det_basis_change`.

* `natCard_quot_LM`: `[ℤ^ι : LM c] = sqN c` for primitive `c`.  Primitivity of `c` says the linear
  functional `φ = ⟨·, c⟩ : ℤ^ι → ℤ` is *surjective* (Bezout, `Finset.gcd_eq_sum_mul`).  Since
  `LM c = φ⁻¹((sqN c)ℤ)` is the preimage of a submodule under a surjection, the universal property
  of quotients gives `ℤ^ι ⧸ LM c ≅ ℤ ⧸ (sqN c)ℤ ≅ ZMod (sqN c)`, of cardinality `sqN c`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.FM

/-- For an integral lattice `L ⊆ ℤ^ι` of full rank (witnessed by a `ℤ`-basis indexed by `ι`),
the covolume `detL L` equals its index `[ℤ^ι : L]` in `ℤ^ι`. -/
theorem detL_eq_natCard_quot {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) (bL : Module.Basis ι ℤ L) :
    Work.HP.detL L = (Nat.card ((ι → ℤ) ⧸ L) : ℝ) := by
  classical
  let b : Module.Basis ι ℤ (ι → ℤ) := Pi.basisFun ℤ ι
  let T : Matrix ι ι ℤ := b.toMatrix (Subtype.val ∘ ⇑bL)
  -- The integer Gram matrix of `bL` is `Tᵀ T`, since `b` is the standard orthonormal basis.
  have hG : (Matrix.of (fun i j : ι => ∑ x, ((bL i : L) : ι → ℤ) x * ((bL j : L) : ι → ℤ) x))
      = Matrix.transpose T * T := by
    dsimp only [T, b]
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Module.Basis.toMatrix_apply, Pi.basisFun_repr, Function.comp_apply]
  -- Its real version is the image of the integer one under `ℤ → ℝ`.
  have hgram : (Matrix.of (fun i j : ι =>
        ∑ x, (((bL i : L) : ι → ℤ) x : ℝ) * (((bL j : L) : ι → ℤ) x : ℝ)))
      = (Matrix.transpose T * T).map (Int.castRingHom ℝ) := by
    rw [← hG]
    ext i j
    simp only [Matrix.of_apply, Matrix.map_apply, Int.coe_castRingHom, Int.cast_sum, Int.cast_mul]
  have hdetM : (Matrix.of (fun i j : ι =>
        ∑ x, (((bL i : L) : ι → ℤ) x : ℝ) * (((bL j : L) : ι → ℤ) x : ℝ))).det
      = (T.det : ℝ) ^ 2 := by
    rw [hgram,
      show (Matrix.transpose T * T).map (Int.castRingHom ℝ)
          = (Int.castRingHom ℝ).mapMatrix (Matrix.transpose T * T) from rfl,
      ← RingHom.map_det (Int.castRingHom ℝ) (Matrix.transpose T * T),
      Matrix.det_mul, Matrix.det_transpose]
    simp only [Int.coe_castRingHom, map_mul]
    ring
  have hTdet : T.det = b.det (Subtype.val ∘ ⇑bL) := (Module.Basis.det_apply b _).symm
  calc Work.HP.detL L = Real.sqrt ((Matrix.of (fun i j : ι =>
          ∑ x, (((bL i : L) : ι → ℤ) x : ℝ) * (((bL j : L) : ι → ℤ) x : ℝ))).det) :=
        Work.HP.Lat.detL_basis_gram L bL
    _ = Real.sqrt ((T.det : ℝ) ^ 2) := by rw [hdetM]
    _ = |(T.det : ℝ)| := Real.sqrt_sq_eq_abs _
    _ = ((T.det).natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
    _ = (Nat.card ((ι → ℤ) ⧸ L) : ℝ) := by
        rw [hTdet]; exact_mod_cast Submodule.natAbs_det_basis_change b L bL

/-- The index of `LM c = latMod c (sqN c)` in `ℤ^ι` equals `sqN c`, for primitive `c`. -/
theorem natCard_quot_LM {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℤ)
    (hc : Work.HP.IsPrim c) :
    Nat.card ((ι → ℤ) ⧸ Work.HP.LM c) = Work.HP.sqN c := by
  classical
  let φ : (ι → ℤ) →ₗ[ℤ] ℤ := Fintype.linearCombination ℤ c
  have hφ : ∀ y : ι → ℤ, φ y = ∑ i, y i * c i := by
    intro y; simp only [φ, Fintype.linearCombination_apply, smul_eq_mul]
  -- Primitivity of `c` makes `φ = ⟨·, c⟩` surjective onto `ℤ`.
  have hsurj : Function.Surjective φ := by
    intro m
    obtain ⟨g, hg⟩ := Finset.gcd_eq_sum_mul Finset.univ c
    have hc' : Finset.univ.gcd c = 1 := hc
    have hsum1 : ∑ a, c a * g a = 1 := by
      have h := hg.symm
      rw [hc'] at h
      simpa using h
    refine ⟨fun i => m * g i, ?_⟩
    rw [hφ]
    have h1 : ∑ i, g i * c i = 1 := by
      rw [Finset.sum_congr rfl (fun i _ => mul_comm (g i) (c i))]; exact hsum1
    have h2 : ∑ i, m * g i * c i = m * ∑ i, g i * c i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [h2, h1, mul_one]
  let S : Submodule ℤ ℤ := Submodule.span ℤ {(Work.HP.sqN c : ℤ)}
  have hLM : Work.HP.LM c = Submodule.comap φ S := rfl
  -- The quotient map `ℤ^ι ⧸ LM c → ℤ ⧸ S` is a bijection.
  have hbij : Function.Bijective (Submodule.mapQ (Submodule.comap φ S) S φ le_rfl) := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at hxy
      rw [Submodule.Quotient.eq, Submodule.mem_comap, map_sub]
      exact hxy
    · intro z
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      obtain ⟨y, hy⟩ := hsurj m
      exact ⟨Submodule.Quotient.mk y, by rw [Submodule.mapQ_apply, hy]⟩
  have hq : Nat.card ((ι → ℤ) ⧸ Work.HP.LM c) = Nat.card (ℤ ⧸ S) := by
    rw [hLM]
    exact Nat.card_congr
      (Equiv.ofBijective (Submodule.mapQ (Submodule.comap φ S) S φ le_rfl) hbij)
  rw [hq]
  have hfin : Nat.card (ℤ ⧸ S) = Nat.card (ZMod (Work.HP.sqN c)) :=
    Nat.card_congr (Int.quotientSpanNatEquivZMod (Work.HP.sqN c)).toEquiv
  rw [hfin, Nat.card_zmod]

theorem detL_LM {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℤ) (hc : Work.HP.IsPrim c) :
    Work.HP.detL (Work.HP.LM c) = (Work.HP.sqN c : ℝ) := by
  have hcard : Nat.card ((ι → ℤ) ⧸ Work.HP.LM c) = Work.HP.sqN c := natCard_quot_LM c hc
  have hne : Nat.card ((ι → ℤ) ⧸ Work.HP.LM c) ≠ 0 := by
    rw [hcard]; exact ne_of_gt (Work.HP.sqN_pos hc)
  have hfin : Finite ((ι → ℤ) ⧸ Work.HP.LM c) := (Nat.card_ne_zero.mp hne).2
  -- A full-rank sublattice of `ℤ^ι`: its finrank is `card ι`.
  have hfr : Module.finrank ℤ (Work.HP.LM c) = Fintype.card ι := by
    rw [(Submodule.finiteQuotient_iff (Work.HP.LM c)).mp hfin,
      Module.finrank_eq_card_basis (Pi.basisFun ℤ ι)]
  obtain ⟨n, b0⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) (Work.HP.LM c)
  have h1 : Module.finrank ℤ (Work.HP.LM c) = n := by
    rw [Module.finrank_eq_card_basis b0, Fintype.card_fin]
  have hn : n = Fintype.card ι := h1.symm.trans hfr
  let e : Fin n ≃ ι := (finCongr hn).trans (Fintype.equivFin ι).symm
  let bL : Module.Basis ι ℤ (Work.HP.LM c) := b0.reindex e
  rw [detL_eq_natCard_quot (Work.HP.LM c) bL, hcard]

end Work.HP.FM
