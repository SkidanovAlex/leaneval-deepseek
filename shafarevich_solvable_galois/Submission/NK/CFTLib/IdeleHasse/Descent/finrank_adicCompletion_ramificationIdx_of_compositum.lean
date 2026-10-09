import Mathlib
import Submission.NK.CFTLib.IdeleHasse.localNormSubgroup
import Submission.NK.CFTLib.IdeleHasse.Crux.cyclotomicAuxiliary
import Submission.NK.CFTLib.IdeleHasse.Descent.cyclotomicLocalDegree
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.absNorm_eq_pow_inertiaDeg_of_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local degree of the compositum `E = L·M` over `M_w` at a place over `Q`

Let `E = L·M` be a compositum of two Galois extensions of the number field `K`, where
`M = K(ζ_l)` and `E = L(ζ_l)` are cyclotomic of the prime conductor `l`, and let `Q` be a
place of `K` prime to `l` (i.e. `l ∤ NQ`), `w | Q` a place of `M`, `q' | w` a place of `E`.
Then

`[E_{q'} : M_w] = e(q' ∩ L | Q)`.

Since `l ∤ NQ`, both `M/K` and `E/L` are unramified at the relevant places
(`cyclotomicLocalDegree`), and the two towers `K ⊂ M ⊂ E` and `K ⊂ L ⊂ E` compute the
ramification index and the inertia degree of `q'`.  The ramification indices give
`e(q'|M) = e(q' ∩ L|K)` at once; for the inertia degrees one uses
`f(q' ∩ L|K) ∣ [L:K]` (Mathlib's Galois fundamental identity
`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn` together with
`IsGalois.card_aut_eq_finrank`), the hypothesis `[L:K] ∣ f(w|Q)`, and the order arithmetic
`orderOf (n ^ a) = orderOf n / a` for `a ∣ orderOf n`, to conclude `f(q'|w) = 1`.
The local fundamental identity `[E_{q'}:M_w] = e(q'|w)·f(q'|w)` then finishes the proof.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace NK.CFTLib.IdeleHasse.Descent

/-- The norm of a height-one prime of a number field is at least `2`. -/
private lemma two_le_absNorm {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm Q.asIdeal := by
  have h0 : Ideal.absNorm Q.asIdeal ≠ 0 := fun hc => Q.ne_bot (Ideal.absNorm_eq_zero_iff.mp hc)
  have h1 : Ideal.absNorm Q.asIdeal ≠ 1 := fun hc => Q.isMaximal.ne_top (Ideal.absNorm_eq_one_iff.mp hc)
  omega

/-- If `l` is a rational prime lying in the height-one prime `Q`, then `l ∣ absNorm Q`. -/
private lemma dvd_absNorm_of_mem {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (l : ℕ) (hl : l.Prime)
    (h : (l : 𝓞 K) ∈ Q.asIdeal) : l ∣ Ideal.absNorm Q.asIdeal := by
  have hle : Ideal.span ({(l : 𝓞 K)} : Set (𝓞 K)) ≤ Q.asIdeal := by
    rw [Ideal.span_singleton_le_iff_mem]; exact h
  have hdvd : Ideal.absNorm Q.asIdeal ∣
      Ideal.absNorm (Ideal.span ({(l : 𝓞 K)} : Set (𝓞 K))) :=
    Ideal.absNorm_dvd_absNorm_of_le hle
  rw [Ideal.absNorm_span_natCast] at hdvd
  obtain ⟨p, hp, hpdvd⟩ :=
    Nat.exists_prime_and_dvd (n := Ideal.absNorm Q.asIdeal) (by have := two_le_absNorm Q; omega)
  have hpq : p = l :=
    (hl.eq_one_or_self_of_dvd p (hp.dvd_of_dvd_pow (hpdvd.trans hdvd))).resolve_left hp.ne_one
  exact hpq ▸ hpdvd

/-- **The local degree of the compositum `E = L·M` over `M_w` is the ramification index of
`q' ∩ 𝓞 L` over `Q`.** -/
theorem finrank_adicCompletion_ramificationIdx_of_compositum {K L M E : Type} [Field K]
    [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M] [Field E] [NumberField E]
    [Algebra K L] [Algebra K M] [Algebra K E] [Algebra L E] [Algebra M E]
    [IsScalarTower K L E] [IsScalarTower K M E]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K M] [IsGalois K E]
    (hgen : Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤)
    {l : ℕ} (hl : l.Prime) [IsCyclotomicExtension {l} K M] [IsCyclotomicExtension {l} L E]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hcop : Nat.Coprime (Ideal.absNorm Q.asIdeal) l)
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (hw : w.asIdeal.LiesOver Q.asIdeal)
    (hdvd : Module.finrank K L ∣ w.asIdeal.inertiaDeg (NumberField.RingOfIntegers K))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hq' : q'.asIdeal.LiesOver w.asIdeal) :
    @Module.finrank (w.adicCompletion M) (q'.adicCompletion E) _ _
        (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap w q' hq')).toModule =
      (q'.asIdeal.under (NumberField.RingOfIntegers L)).ramificationIdx
        (NumberField.RingOfIntegers K) := by
  classical
  haveI hEffd : FiniteDimensional L E := inferInstance
  haveI hpi : q'.asIdeal.LiesOver w.asIdeal := hq'
  haveI hwi : w.asIdeal.LiesOver Q.asIdeal := hw
  -- ## `l` does not lie in `Q` (and hence in no place above it)
  have hlQ : (l : 𝓞 K) ∉ Q.asIdeal := by
    intro hmem
    have hdvd : l ∣ Ideal.absNorm Q.asIdeal := dvd_absNorm_of_mem Q l hl hmem
    have hg : Nat.gcd (Ideal.absNorm Q.asIdeal) l = 1 := hcop.gcd_eq_one
    have h1 : l ∣ Nat.gcd (Ideal.absNorm Q.asIdeal) l := Nat.dvd_gcd hdvd (dvd_refl l)
    rw [hg] at h1
    exact hl.not_dvd_one h1
  -- ## the place `r` of `L` below `q'`
  have h1 : q'.asIdeal.under (𝓞 K) = w.asIdeal.under (𝓞 K) := by
    rw [hq'.over, Ideal.under_under]
  have hQunder : Q.asIdeal = (q'.asIdeal.under (𝓞 L)).under (𝓞 K) := by
    rw [hw.over, ← h1, Ideal.under_under]
  haveI hLiesRL_Q : (q'.asIdeal.under (𝓞 L)).LiesOver Q.asIdeal := ⟨hQunder⟩
  have hprimeL : (q'.asIdeal.under (𝓞 L)).IsPrime := inferInstance
  have hneL : q'.asIdeal.under (𝓞 L) ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot Q.ne_bot (q'.asIdeal.under (𝓞 L))
  let rl : IsDedekindDomain.HeightOneSpectrum (𝓞 L) :=
    ⟨q'.asIdeal.under (𝓞 L), hprimeL, hneL⟩
  have hqL : (l : 𝓞 L) ∉ rl.asIdeal := by
    intro hmem
    refine hlQ ?_
    rw [hQunder, Ideal.mem_under, map_natCast]
    exact hmem
  -- ## the cyclotomic inputs: `M/K` and `E/L` are unramified at the relevant places
  obtain ⟨heM, hfM⟩ :=
    NK.CFTLib.IdeleHasse.Descent.cyclotomicLocalDegree Q l hl hlQ w hw
  obtain ⟨heL, hfL⟩ :=
    NK.CFTLib.IdeleHasse.Descent.cyclotomicLocalDegree rl l hl hqL q' inferInstance
  -- ## ramification indices: `e(q'|𝓞 M) = e(rl|𝓞 K)`
  have htowerM : q'.asIdeal.ramificationIdx (𝓞 K) =
      w.asIdeal.ramificationIdx (𝓞 K) * q'.asIdeal.ramificationIdx (𝓞 M) :=
    Ideal.ramificationIdx_tower (R := 𝓞 K) (S := 𝓞 M) (T := 𝓞 E)
      (q := w.asIdeal) (r := q'.asIdeal)
  have htowerL : q'.asIdeal.ramificationIdx (𝓞 K) =
      (q'.asIdeal.under (𝓞 L)).ramificationIdx (𝓞 K) *
        q'.asIdeal.ramificationIdx (𝓞 L) :=
    Ideal.ramificationIdx_tower (R := 𝓞 K) (S := 𝓞 L) (T := 𝓞 E)
      (q := q'.asIdeal.under (𝓞 L)) (r := q'.asIdeal)
  have he : q'.asIdeal.ramificationIdx (𝓞 M) =
      (q'.asIdeal.under (𝓞 L)).ramificationIdx (𝓞 K) := by
    rw [heM, one_mul] at htowerM
    rw [heL, mul_one] at htowerL
    omega
  -- ## inertia degrees: `f(q'|𝓞 M) = 1`
  have hdtowerM : q'.asIdeal.inertiaDeg (𝓞 K) =
      w.asIdeal.inertiaDeg (𝓞 K) * q'.asIdeal.inertiaDeg (𝓞 M) :=
    Ideal.inertiaDeg_tower (R := 𝓞 K) (S := 𝓞 M) (T := 𝓞 E)
      (q := w.asIdeal) (r := q'.asIdeal)
  have hdtowerL : q'.asIdeal.inertiaDeg (𝓞 K) =
      (q'.asIdeal.under (𝓞 L)).inertiaDeg (𝓞 K) *
        q'.asIdeal.inertiaDeg (𝓞 L) :=
    Ideal.inertiaDeg_tower (R := 𝓞 K) (S := 𝓞 L) (T := 𝓞 E)
      (q := q'.asIdeal.under (𝓞 L)) (r := q'.asIdeal)
  -- `f(rl|Q) ∣ [L:K]` (Galois fundamental identity), hence `f(rl|Q) ∣ f(w|Q)`
  have hfLdvdK : (q'.asIdeal.under (𝓞 L)).inertiaDeg (𝓞 K) ∣ Module.finrank K L := by
    haveI : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) := inferInstance
    have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      Q.asIdeal (𝓞 L) Gal(L/K)
    rw [Ideal.inertiaDegIn_eq_inertiaDeg Q.asIdeal (q'.asIdeal.under (𝓞 L)) Gal(L/K),
      IsGalois.card_aut_eq_finrank] at h
    exact ⟨(Ideal.primesOver Q.asIdeal (𝓞 L)).ncard *
        Ideal.ramificationIdxIn Q.asIdeal (𝓞 L), by rw [← h]; ring⟩
  have hfLdvd : (q'.asIdeal.under (𝓞 L)).inertiaDeg (𝓞 K) ∣
      w.asIdeal.inertiaDeg (𝓞 K) := hfLdvdK.trans hdvd
  have hfLdvdOrd : (q'.asIdeal.under (𝓞 L)).inertiaDeg (𝓞 K) ∣
      orderOf ((Ideal.absNorm Q.asIdeal : ℕ) : ZMod l) := hfM ▸ hfLdvd
  have habs : Ideal.absNorm rl.asIdeal =
      Ideal.absNorm Q.asIdeal ^
        (q'.asIdeal.under (𝓞 L)).inertiaDeg (𝓞 K) :=
    Commons.NumberTheory.NumberField.absNorm_eq_pow_inertiaDeg_of_liesOver Q rl hLiesRL_Q
  have hfLne : (q'.asIdeal.under (𝓞 L)).inertiaDeg (𝓞 K) ≠ 0 :=
    (Ideal.inertiaDeg_pos (q := q'.asIdeal.under (𝓞 L)) (R := 𝓞 K)).ne'
  -- `f(q'|𝓞 L) = f(w|𝓞 K) / f(rl|𝓞 K)`, hence `f(q'|𝓞 K) = f(w|𝓞 K)`
  have horder : q'.asIdeal.inertiaDeg (𝓞 L) =
      w.asIdeal.inertiaDeg (𝓞 K) /
        (q'.asIdeal.under (𝓞 L)).inertiaDeg (𝓞 K) := by
    rw [hfL, habs, Nat.cast_pow]
    rw [hfM, orderOf_pow' _ hfLne, Nat.gcd_eq_right hfLdvdOrd]
  have hdegL : q'.asIdeal.inertiaDeg (𝓞 K) = w.asIdeal.inertiaDeg (𝓞 K) := by
    rw [hdtowerL, horder, Nat.mul_div_cancel' hfLdvd]
  have hfMone : q'.asIdeal.inertiaDeg (𝓞 M) = 1 := by
    have hpos : 0 < q'.asIdeal.inertiaDeg (𝓞 K) :=
      Ideal.inertiaDeg_pos (q := q'.asIdeal) (R := 𝓞 K)
    have h : q'.asIdeal.inertiaDeg (𝓞 K) =
        q'.asIdeal.inertiaDeg (𝓞 K) * q'.asIdeal.inertiaDeg (𝓞 M) :=
      hdtowerM.trans (congrArg
        (fun x => x * q'.asIdeal.inertiaDeg (𝓞 M)) hdegL.symm)
    have h2 : q'.asIdeal.inertiaDeg (𝓞 K) * 1 =
        q'.asIdeal.inertiaDeg (𝓞 K) * q'.asIdeal.inertiaDeg (𝓞 M) := by
      rw [mul_one]; exact h
    exact (Nat.eq_of_mul_eq_mul_left hpos h2).symm
  -- ## the local fundamental identity at `q' | w`
  have hfin :=
    Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      (K := M) (L := E) w q' hq'
  rw [he, hfMone, mul_one] at hfin
  exact hfin.symm

end NK.CFTLib.IdeleHasse.Descent
