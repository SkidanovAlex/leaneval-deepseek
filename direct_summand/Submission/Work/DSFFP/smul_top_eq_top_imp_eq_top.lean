import Mathlib
import Submission.Work.DSFFP.Defs

namespace Work.DSFFP

/-- For an ideal `I` of a commutative ring `R` and an ideal `J` of `R ⧸ I`, the image of `J`
in `R ⧸ I` is the unit ideal if and only if `I ⊔ J = ⊤`. -/
lemma map_quotientMk_eq_top_iff {R : Type*} [CommRing R] (I J : Ideal R) :
    Ideal.map (Ideal.Quotient.mk I) J = ⊤ ↔ I ⊔ J = ⊤ := by
  constructor
  · intro hh
    have h' := congrArg (Ideal.comap (Ideal.Quotient.mk I)) hh
    rwa [Ideal.comap_map_quotientMk, Ideal.comap_top] at h'
  · intro hh
    rw [← Ideal.map_top (Ideal.Quotient.mk I), ← hh, Ideal.map_sup, Ideal.map_quotient_self,
      bot_sup_eq]

/-- Base change of ideals commutes with passage to the quotient `R ⧸ I`, for an `R`-algebra `A`
which is also an `R ⧸ I`-algebra in the compatible way recorded in `hcomp`. -/
lemma map_algebraMap_quotient_eq {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal R) [Algebra (R ⧸ I) A]
    (hcomp : (algebraMap (R ⧸ I) A).comp (Ideal.Quotient.mk I) = algebraMap R A)
    (J : Ideal (R ⧸ I)) :
    Ideal.map (algebraMap (R ⧸ I) A) J
      = Ideal.map (algebraMap R A) (J.comap (Ideal.Quotient.mk I)) := by
  calc Ideal.map (algebraMap (R ⧸ I) A) J
      = Ideal.map (algebraMap (R ⧸ I) A)
          (Ideal.map (Ideal.Quotient.mk I) (J.comap (Ideal.Quotient.mk I))) := by
        rw [Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective]
    _ = Ideal.map ((algebraMap (R ⧸ I) A).comp (Ideal.Quotient.mk I))
          (J.comap (Ideal.Quotient.mk I)) := by
        rw [Ideal.map_map]
    _ = Ideal.map (algebraMap R A) (J.comap (Ideal.Quotient.mk I)) := by
        rw [hcomp]

/-- **Faithfulness modulo a power of an ideal, from faithfulness modulo the ideal.**
Let `A` be a commutative `R`-algebra, `I ⊆ R` an ideal and `n ≥ 1`.  If `A ⧸ IA` is faithfully
flat over `R ⧸ I`, then for any ideal `K` with `K = I ^ n`, an ideal `J` of `R ⧸ K` whose
extension to `A ⧸ KA` is the unit ideal must already be the unit ideal. -/
theorem smul_top_eq_top_of_faithfullyFlat_quotient {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (I K : Ideal R) (n : ℕ) (hn : 1 ≤ n) (hK : K = I ^ n)
    (h : Module.FaithfullyFlat (R ⧸ I) (A ⧸ I.map (algebraMap R A)))
    {J : Ideal (R ⧸ K)}
    (hJ : J • (⊤ : Submodule (R ⧸ K) (A ⧸ K.map (algebraMap R A))) = ⊤) :
    J = ⊤ := by
  set Jt : Ideal R := J.comap (Ideal.Quotient.mk K) with hJt
  have hKleI : K ≤ I := by
    rw [hK]
    obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [pow_succ]
    exact Ideal.mul_le_right
  have hJmap : Ideal.map (algebraMap (R ⧸ K) (A ⧸ K.map (algebraMap R A))) J = ⊤ := by
    simpa only [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff] using hJ
  have hJtmap : Ideal.map (Ideal.Quotient.mk K) Jt = J :=
    Ideal.map_comap_of_surjective (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective J
  have hKleJt : K ≤ Jt :=
    (Ideal.map_le_iff_le_comap (f := Ideal.Quotient.mk K)).mp (by simp)
  have h4' : Ideal.map (algebraMap (R ⧸ K) (A ⧸ K.map (algebraMap R A))) J
      = Ideal.map (algebraMap R (A ⧸ K.map (algebraMap R A))) Jt :=
    map_algebraMap_quotient_eq K (RingHom.ext fun _ => rfl) J
  have h4 : Ideal.map (algebraMap R (A ⧸ K.map (algebraMap R A))) Jt = ⊤ := by
    rw [← h4', hJmap]
  set B : Ideal A := Ideal.map (algebraMap R A) Jt with hB
  have hcompK : algebraMap R (A ⧸ K.map (algebraMap R A))
      = (Ideal.Quotient.mk (K.map (algebraMap R A))).comp (algebraMap R A) :=
    RingHom.ext fun _ => rfl
  have h5 : Ideal.map (Ideal.Quotient.mk (K.map (algebraMap R A))) B = ⊤ := by
    rw [hB, Ideal.map_map, ← hcompK]
    exact h4
  have h6 : K.map (algebraMap R A) ⊔ B = ⊤ :=
    (map_quotientMk_eq_top_iff (K.map (algebraMap R A)) B).mp h5
  have h7 : Ideal.map (algebraMap R A) I ⊔ B = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← h6]
    exact sup_le_sup_right (Ideal.map_mono hKleI) B
  set Ibar : Ideal (R ⧸ I) := Ideal.map (Ideal.Quotient.mk I) Jt with hIbar
  have hcompI : algebraMap R (A ⧸ I.map (algebraMap R A))
      = (Ideal.Quotient.mk (I.map (algebraMap R A))).comp (algebraMap R A) :=
    RingHom.ext fun _ => rfl
  have h8 : Ideal.map (algebraMap (R ⧸ I) (A ⧸ I.map (algebraMap R A))) Ibar = ⊤ := by
    have key : Ideal.map (algebraMap (R ⧸ I) (A ⧸ I.map (algebraMap R A))) Ibar
        = Ideal.map (algebraMap R (A ⧸ I.map (algebraMap R A))) (I ⊔ Jt) := by
      rw [hIbar,
        map_algebraMap_quotient_eq I (RingHom.ext fun _ => rfl)
          (Ideal.map (Ideal.Quotient.mk I) Jt),
        Ideal.comap_map_quotientMk]
    rw [key, hcompI, ← Ideal.map_map, Ideal.map_sup, ← hB, h7, Ideal.map_top]
  have h9 : Ibar = ⊤ := by
    have hff := (Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top (R ⧸ I)
      (A ⧸ I.map (algebraMap R A))).mp h
    exact hff.2 Ibar (by
      simpa only [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff] using h8)
  have h10 : I ⊔ Jt = ⊤ := (map_quotientMk_eq_top_iff I Jt).mp h9
  have h11 : K ⊔ Jt = ⊤ := by
    rw [hK]
    exact Ideal.pow_sup_eq_top h10
  have h12 : Jt = ⊤ := by
    rw [← sup_eq_right.mpr hKleJt]
    exact h11
  rw [← hJtmap, h12, Ideal.map_top]

/-- The faithfulness (support) part of the FFP node: with `S = D ⧸ (p)ᵐ` and `T = D' ⧸ (p)ᵐD'`, any ideal `J ≤ S` with `J • ⊤ = ⊤` in `T` must be all of `S`, granted that `D' ⧸ (p)D'` is faithfully flat over `D ⧸ (p)`.

PLAN for the prover (write it at `Submission/Work/DSFFP/smul_top_eq_top_imp_eq_top.lean`).
Let `J` be an ideal of `S` with `J • ⊤ = ⊤` in `T` and let `J̃ ⊆ D` be its preimage under `D ↠ D ⧸ (p)ᵐ`.  Then `J̃ + (p)ᵐ = D`.
* Reducing modulo `p`: the image of `J • ⊤` under `T ↠ T ⧸ (p) • ⊤ ≅ D' ⧸ (p)D'` is `J̃ · (D' ⧸ (p)D')` (use `(J̃ + (p)ᵐ)·D'` and `(p)ᵐ·D' ⊆ pD'`), hence `= ⊤`.
* The ideal `(J̃ + (p)D)/(p)D` of `D ⧸ (p)` generates the unit ideal in `D' ⧸ (p)D'`, so `Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top` (or `.iff_flat_and_proper_ideal`) applied to the hypothesis `h` gives `(J̃ + (p)D)/(p)D = ⊤`, i.e. `J̃ + (p)D = D`.
* The binomial expansion gives `D = (J̃ + (p)D)^m ⊆ J̃ + (p)^m D`, so `J̃ + (p)^mD = D`.  Passing to `S = D ⧸ (p)^mD` (i.e. `Submodule.quotientQuotientEquivQuotient`/`Ideal.Quotient` bookkeeping) yields `J = ⊤`.
For `m = 0` the ring `S` is trivial, so every ideal is `⊤` and the claim is immediate. -/
theorem smul_top_eq_top_imp_eq_top {D D' : Type _} [CommRing D] [CommRing D'] [Algebra D D']
    (p : ℕ) (h : Module.FaithfullyFlat (D ⧸ Ideal.span {(p : D)})
      (D' ⧸ (Ideal.span {(p : D)}).map (algebraMap D D'))) (m : ℕ)
    {J : Ideal (D ⧸ Ideal.span {(p : D) ^ m})}
    (hJ : J • (⊤ : Submodule (D ⧸ Ideal.span {(p : D) ^ m})
      (D' ⧸ (Ideal.span {(p : D) ^ m}).map (algebraMap D D'))) = ⊤) : J = ⊤ := by
  rcases m with _ | m'
  · have hsub : Subsingleton (D ⧸ Ideal.span {(p : D) ^ 0}) := by
      rw [pow_zero, Ideal.span_singleton_one]
      infer_instance
    rw [← top_le_iff]
    intro x _
    have hx : x = 0 := @Subsingleton.elim _ hsub x 0
    rw [hx]
    exact J.zero_mem
  · exact smul_top_eq_top_of_faithfullyFlat_quotient (I := Ideal.span {(p : D)})
      (K := Ideal.span {(p : D) ^ (m' + 1)}) (n := m' + 1)
      (by omega) (Ideal.span_singleton_pow (p : D) (m' + 1)).symm h hJ

end Work.DSFFP
