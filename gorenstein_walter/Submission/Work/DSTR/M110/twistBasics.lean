import Mathlib
import Submission.Work.DSTR.M110.PiCoreFacts
import Submission.Work.DSTR.M110.SylowGen
import Submission.Work.DSTR.M110.Aut.pglIndex
import Submission.Work.DSTR.M110.Aut.centralizer
import Submission.Work.DSTR.M110.Galois.decomposition
import Submission.Work.DSTR.M110.SplitCase.GaloisPart
import Submission.Work.DSTR.M110.Conj
import Submission.Work.DSTR.M110.Stabilizer
import Submission.Work.DSTR.M110.Normalizer.Defs

/-!
# Twist case of DS10a (`D110iiModelProp`)

Basic helper lemmas for the twist case of DS10a (`D110iiModelProp`):
odd-order elements of `pglImage`, the `p`-group of translations centralizing `t`, and the
commutative-algebra computation `(transl c) ^ n = transl (n * c)`.
-/

namespace Work.DSTR.M110

open Work.AUTL2

variable {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
  [DecidableEq (GaloisField p k)]

/-- Every element of an `r`-group with `r` odd has odd order. -/
lemma odd_orderOf_of_mem_isPGroup {G : Type*} [Group G] (r : ℕ) (hr : Odd r) (N : Subgroup G)
    (hNr : IsPGroup r N) {x : G} (hx : x ∈ N) : Odd (orderOf x) := by
  obtain ⟨n, hn⟩ := hNr ⟨x, hx⟩
  have h1 : orderOf (⟨x, hx⟩ : ↥N) ∣ r ^ n := orderOf_dvd_iff_pow_eq_one.mpr hn
  rw [Subgroup.orderOf_mk] at h1
  exact Odd.of_dvd_nat (hr.pow) h1

/-- An element of `pglImage F` of odd order lies in `pslImage F`
(`PGL(2,F)/PSL(2,F) ≅ Fˣ/(Fˣ)²` has exponent `2`). -/
lemma mem_pslImage_of_odd_of_mem_pglImage (x : Equiv.Perm (P1 (GaloisField p k)))
    (hx : x ∈ pglImage (GaloisField p k)) (hodd : Odd (orderOf x)) :
    x ∈ pslImage (GaloisField p k) := by
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  set x : Equiv.Perm (P1 (GaloisField p k)) :=
    pglHom _ (Matrix.ProjGenLinGroup.mk B) with hxdef
  have hsq : x * x ∈ pslImage (GaloisField p k) := by
    have hxx : x * x = pglHom _ (Matrix.ProjGenLinGroup.mk (B * B)) := by
      rw [hxdef, ← map_mul, ← map_mul]
    rw [hxx, Work.AUTL2.Aut.mem_pslImage_iff_isSquare_det]
    exact ⟨B.det, by rw [map_mul]⟩
  have hm : x ^ orderOf x = 1 := pow_orderOf_eq_one x
  obtain ⟨s, hs⟩ := hodd
  have h2 : 2 * ((orderOf x + 1) / 2) = orderOf x + 1 := by omega
  have hsplit : x = (x * x) ^ ((orderOf x + 1) / 2) := by
    calc x = x ^ (orderOf x + 1) := by rw [pow_succ, hm, one_mul]
      _ = x ^ (2 * ((orderOf x + 1) / 2)) := by rw [h2]
      _ = (x * x) ^ ((orderOf x + 1) / 2) := by rw [pow_mul, pow_two]
  rw [hsplit]
  exact Subgroup.pow_mem _ hsq _

/-- `pglImage F` is normal in `pgammaL F`. -/
lemma conj_mem_pglImage {g : Equiv.Perm (P1 (GaloisField p k))}
    (hg : g ∈ pgammaL (GaloisField p k)) {y : Equiv.Perm (P1 (GaloisField p k))}
    (hy : y ∈ pglImage (GaloisField p k)) : g * y * g⁻¹ ∈ pglImage (GaloisField p k) := by
  have hnorm : pgammaL (GaloisField p k) ≤
      Subgroup.normalizer (pglImage (GaloisField p k) : Set _) := by
    rw [pgammaL]
    exact sup_le Subgroup.le_normalizer (Galois.galSub_le_normalizer_pglImage _)
  exact (Subgroup.le_normalizer_iff.mp hnorm) g hg y hy

/-- `(transl c) ^ n = transl (n * c)`. -/
lemma transl_pow (c : GaloisField p k) (n : ℕ) :
    (transl (GaloisField p k) c) ^ n
      = transl (GaloisField p k) ((n : GaloisField p k) * c) := by
  induction n with
  | zero => simp [transl_zero]
  | succ n ih =>
      rw [pow_succ, ih, transl_mul]
      congr 1
      push_cast
      ring

/-- The subgroup of translations centralizing `t` is a `p`-group. -/
lemma isPGroup_translCent (t : Equiv.Perm (P1 (GaloisField p k))) :
    IsPGroup p ↥(Normalizer.translSub (GaloisField p k) ⊓
      Subgroup.centralizer ({t} : Set (Equiv.Perm (P1 (GaloisField p k))))) := by
  haveI : CharP (GaloisField p k) p := inferInstance
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one]
  obtain ⟨c, hc⟩ := (Normalizer.mem_translSub_iff (GaloisField p k)).mp g.2.1
  have hgc : (g : Equiv.Perm (P1 (GaloisField p k))) = transl (GaloisField p k) c := hc.symm
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, hgc, transl_pow, CharP.cast_eq_zero, zero_mul,
    transl_zero]


end Work.DSTR.M110
