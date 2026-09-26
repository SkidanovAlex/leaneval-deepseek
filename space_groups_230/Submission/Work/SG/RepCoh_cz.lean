import Mathlib
import Submission.Work.SG.SGRepDefs
import Submission.Work.SG.CzAux.mulV_ediv
import Submission.Work.SG.CzAux.dvd_eM

/-!
# `RepCoh_cz`: the integral coboundary model satisfies the cocycle recursion

For the arithmetic class `j` with point-group order `n = (Ad j).n` and a vector `σ : Data.V3`
(the numerator of the translation `s = σ/n²`), the coboundary model of
`Submission/Work/SG/SGRepDefs.lean` is

`cz j σ i = ((1 - e_i) σ) / n`   (componentwise integer division),

and the lemma proved here is the coherence statement needed by the `applyB` recursion
(`RepCoh_applyB`): `cz j σ 0 = 0`, and for every generator `g` and every table index `i`, the
vector

  `(1 - e_{g·i}) σ / n  -  ( (1 - g) σ / n  +  g · ((1 - e_i) σ / n) )`

is divisible by `n`.  This is the rearrangement

  `(1 - g e_i) = (1 - g) + g (1 - e_i)`

of the coboundary identity `δ(σ/n²)(g, i) = 0`, made integral.

The only non-formal input is the hypothesis `hσ`: `n ∣ (1 - g) σ` for every *generator* `g`.
It is propagated from the generators to every element of the BFS element table `elems` by the
delegated lemma `Work.SG.CzAux.dvd_eM` (imported above), using `elems[0] = 1`, the BFS relation
`elems[i+1] = gens[par1 i] · elems[par2 i]` with `par2 i ≤ i` (`Ad_par_rel3`), and the identity
`(1 - MN)σ = (1 - M)σ + M((1 - N)σ)`.
-/

namespace Work.SG

/-! Flat `V3`/`M3` algebra used by the coboundary model `RC.cz`. -/
namespace RepCoh_cz_aux

/-! ### The bridge to `Fin 3 → ℤ` -/

theorem toFun_add (u v : Data.V3) : (Data.V3.add u v).toFun = u.toFun + v.toFun := by
  funext c; fin_cases c <;> rfl

theorem toFun_sub (u v : Data.V3) : (Data.V3.sub u v).toFun = u.toFun - v.toFun := by
  funext c; fin_cases c <;> rfl

theorem toFun_zero : Data.V3.zero.toFun = (0 : Fin 3 → ℤ) := by
  funext c; fin_cases c <;> rfl

theorem toFun_ediv (v : Data.V3) (n : ℤ) :
    (Data.V3.ediv v n).toFun = fun c => v.toFun c / n := by
  funext c; fin_cases c <;> rfl

/-! ### Algebra of the matrix action (through the `Matrix` bridge `CZ.toIMat_mulV`) -/

theorem mulV_one (v : Data.V3) : Data.M3.mulV Data.M3.one v = v := by
  apply CZ.toFun_inj
  simp only [CZ.toIMat_mulV, CZ.toIMat_one, Matrix.one_mulVec]

theorem mulV_mul (A B : Data.M3) (v : Data.V3) :
    Data.M3.mulV (Data.M3.mul A B) v = Data.M3.mulV A (Data.M3.mulV B v) := by
  apply CZ.toFun_inj
  simp only [CZ.toIMat_mulV, CZ.toIMat_mul, ← Matrix.mulVec_mulVec]

theorem mulV_sub (A : Data.M3) (u v : Data.V3) :
    Data.M3.mulV A (Data.V3.sub u v)
      = Data.V3.sub (Data.M3.mulV A u) (Data.M3.mulV A v) := by
  apply CZ.toFun_inj
  simp only [CZ.toIMat_mulV, toFun_sub, Matrix.mulVec_sub]

theorem sub_self' (u : Data.V3) : Data.V3.sub u u = Data.V3.zero := by
  apply CZ.toFun_inj
  simp only [toFun_sub, toFun_zero, sub_self]

/-- `(u - v) + (v - w) = u - w`. -/
theorem add_sub_sub (u v w : Data.V3) :
    Data.V3.add (Data.V3.sub u v) (Data.V3.sub v w) = Data.V3.sub u w := by
  apply CZ.toFun_inj
  simp only [toFun_add, toFun_sub]
  abel

/-! ### Divisibility -/

theorem dvd_zero' (n : ℤ) : Data.V3.dvd n Data.V3.zero = true :=
  (RC.dvd_iff_toFun n _).mpr (fun c => by fin_cases c <;> simp [Data.V3.toFun, Data.V3.zero])

theorem dvd_add' {n : ℤ} {u v : Data.V3} (hu : Data.V3.dvd n u = true)
    (hv : Data.V3.dvd n v = true) : Data.V3.dvd n (Data.V3.add u v) = true :=
  (RC.dvd_iff_toFun n _).mpr (fun c => by
    have h1 := (RC.dvd_iff_toFun n u).mp hu c
    have h2 := (RC.dvd_iff_toFun n v).mp hv c
    rw [toFun_add]
    exact Int.dvd_add h1 h2)

/-- An integral matrix preserves divisibility of a vector. -/
theorem dvd_mulV' {n : ℤ} (A : Data.M3) {v : Data.V3} (hv : Data.V3.dvd n v = true) :
    Data.V3.dvd n (Data.M3.mulV A v) = true :=
  (RC.dvd_iff_toFun n _).mpr (fun c => by
    rw [CZ.toIMat_mulV]
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.dvd_sum (fun k _ =>
      dvd_mul_of_dvd_right ((RC.dvd_iff_toFun n v).mp hv k) (A.toIMat c k)))

/-! ### Division versus the linear action -/

/-- Division is additive on divisible vectors.  (Division versus the integral linear action is
the delegated lemma `Work.SG.CzAux.mulV_ediv`, imported above.) -/
theorem ediv_add' {n : ℤ} {u v : Data.V3} (hu : Data.V3.dvd n u = true)
    (_hv : Data.V3.dvd n v = true) :
    Data.V3.ediv (Data.V3.add u v) n = Data.V3.add (Data.V3.ediv u n) (Data.V3.ediv v n) := by
  apply CZ.toFun_inj
  simp only [toFun_ediv, toFun_add]
  funext c
  exact Int.add_ediv_of_dvd_left ((RC.dvd_iff_toFun n u).mp hu c)

end RepCoh_cz_aux

theorem RepCoh_cz (j : Fin 73) (σ : Data.V3)
    (hσ : ∀ g, g < Work.SG.RC.KK j →
      Data.V3.dvd ((Work.SG.RC.Ad j).n) (Data.V3.sub σ (Data.M3.mulV (Work.SG.RC.gMt j g) σ)) = true) :
    (Work.SG.RC.cz j σ 0 = 0) ∧
    (∀ g, g < Work.SG.RC.KK j → ∀ i, i < Work.SG.RC.N j →
      Data.V3.dvd ((Work.SG.RC.Ad j).n) (Data.V3.sub (CZ.ofFun (Work.SG.RC.cz j σ (Work.SG.RC.mulg j g i)))
        (Data.V3.add (CZ.ofFun (Work.SG.RC.cz j σ (Work.SG.RC.geni j g)))
          (Data.M3.mulV (Work.SG.RC.gMt j g) (CZ.ofFun (Work.SG.RC.cz j σ i))))) = true) := by
  refine ⟨?_, ?_⟩
  · -- `cz j σ 0 = 0`
    funext c
    have h0 : RC.eM j 0 = Data.M3.one := by
      apply CZ.toIMat_inj
      rw [show (RC.eM j 0).toIMat = 1 from RC.e_one j, CZ.toIMat_one]
    fin_cases c <;>
      simp [RC.cz, h0, RepCoh_cz_aux.mulV_one, RepCoh_cz_aux.sub_self',
        Data.V3.ediv, Data.V3.zero, Data.V3.toFun]
  · -- the integral cocycle recursion
    intro g hg i hi
    have hg' : g < (RC.Ad j).gens.length := hg
    have hmulg : RC.eM j (RC.mulg j g i) = Data.M3.mul (RC.gMt j g) (RC.eM j i) := by
      have h := RC.Ad_mulGen_rel j g hg' i hi
      simpa only [RC.eM, RC.gMt, RC.mulg] using h
    have hgeni : RC.eM j (RC.geni j g) = RC.gMt j g := by
      have h := RC.Ad_genIdx_rel j g hg'
      simpa only [RC.eM, RC.gMt, RC.geni] using h
    have hDi : Data.V3.dvd ((RC.Ad j).n)
        (Data.V3.sub σ (Data.M3.mulV (RC.eM j i) σ)) = true :=
      CzAux.dvd_eM j σ hσ i hi
    have hDA : Data.V3.dvd ((RC.Ad j).n)
        (Data.V3.sub σ (Data.M3.mulV (RC.gMt j g) σ)) = true := hσ g hg
    rw [RC.ofFun_cz, RC.ofFun_cz, RC.ofFun_cz, hmulg, hgeni]
    have hB : Data.V3.add
          (Data.V3.ediv (Data.V3.sub σ (Data.M3.mulV (RC.gMt j g) σ)) ↑(RC.Ad j).n)
          (Data.M3.mulV (RC.gMt j g)
            (Data.V3.ediv (Data.V3.sub σ (Data.M3.mulV (RC.eM j i) σ)) ↑(RC.Ad j).n))
        = Data.V3.ediv
            (Data.V3.sub σ (Data.M3.mulV (Data.M3.mul (RC.gMt j g) (RC.eM j i)) σ))
            ↑(RC.Ad j).n := by
      rw [CzAux.mulV_ediv (RC.gMt j g)
        (Data.V3.sub σ (Data.M3.mulV (RC.eM j i) σ)) ↑(RC.Ad j).n hDi]
      rw [← RepCoh_cz_aux.ediv_add' hDA
        (RepCoh_cz_aux.dvd_mulV' (RC.gMt j g) hDi)]
      congr 1
      rw [RepCoh_cz_aux.mulV_mul, RepCoh_cz_aux.mulV_sub, RepCoh_cz_aux.add_sub_sub]
    rw [hB, RepCoh_cz_aux.sub_self', RepCoh_cz_aux.dvd_zero']

end Work.SG
