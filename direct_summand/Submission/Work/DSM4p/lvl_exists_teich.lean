import Mathlib
import Submission.Work.DSM4p.Plan
import Submission.Work.DSM4p.Lvl
import Submission.Work.DSM4p.lvlP_charP
import Submission.Work.DSM4p.chartLevel_perfect

/-!
# DSM4p — Teichmüller representatives of the untilted levels

This is step **(2)** of the Route U plan (`Submission/Work/DSM4p/Plan.lean`): every class in an
untilt `untiltOf R φ = 𝕎 R ⧸ 𝕎φ(ker θ)` of a perfect ring `R` of characteristic `p` is congruent
**modulo `p`** to a Teichmüller class `[r]`, `r ∈ R`.

The mathematical content is Mathlib's `WittVector.ker_constantCoeff`: for `R` perfect of
characteristic `p`, one has `ker constantCoeff = (p) ⊆ 𝕎 R`, so that for `Y : 𝕎 R`

  `Y - [constantCoeff Y] ∈ (p) ⊆ 𝕎 R`,

whence, passing to the quotient `untiltOf R φ` and using `mk (p : 𝕎 R) = (p : untiltOf R φ)`,

  `mk Y - mk [constantCoeff Y] ∈ (p : untiltOf R φ)`.

The same consideration applies to every quotient of `𝕎 R` — this is why the argument is formulated
once, for an arbitrary `untiltOf` (`exists_teich_of_untiltOf`), and then specialised to the level
`lvl Q hgr N = untiltOf (lvlP Q hgr N) (algebraMap B♭ (lvlP Q hgr N))`.  For the latter the two
hypotheses needed (perfectness and characteristic `p` of `lvlP Q hgr N`) are supplied by
`Work.DSM4p.chartLevel_perfect` and `Work.DSM4p.lvlP_charP`; here the hypothesis `gr 0 ≠ 0` enters,
since for `gr 0 = 0` the level is the zero ring and no prime is its characteristic.
-/

set_option linter.style.haveILetI false

namespace Work.DSM4p

universe a

open DSMap DSMap.Mix DSMap.Mix2

section UntiltOf

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
variable [IsAdicComplete (Ideal.span {(p : W)}) W]

/-- **Teichmüller representatives modulo `p` of an untilt.**  If `R` is perfect of characteristic
`p` (so that `ker (constantCoeff) = (p)` in `𝕎 R`, `WittVector.ker_constantCoeff`) and
`φ : W♭ →+* R` is any ring homomorphism, then every class `y` in the untilt
`untiltOf R φ = 𝕎 R ⧸ 𝕎φ(ker θ_W)` is congruent modulo `p` to the Teichmüller class `[r]` of the
`0`-th Witt coordinate `r` of a lift of `y`. -/
theorem exists_teich_of_untiltOf {R : Type a} [CommRing R] [CharP R p] [PerfectRing R p]
    (φ : PreTilt W p →+* R) (y : DSM5c.untiltOf (p := p) (W := W) R φ) :
    ∃ r : R, y - DSM5c.untiltOf.mk (p := p) (W := W) φ (WittVector.teichmuller p r) ∈
      Ideal.span {((p : DSM5c.untiltOf (p := p) (W := W) R φ))} := by
  -- Lift `y` to a Witt vector `Y`.
  obtain ⟨Y, hY⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨WittVector.constantCoeff Y, ?_⟩
  rw [← hY]
  -- The constant coefficient of a Teichmüller lift is the element itself.
  have hteich : WittVector.constantCoeff
      (WittVector.teichmuller p (WittVector.constantCoeff Y)) =
        WittVector.constantCoeff Y := by
    rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  -- `Y` is congruent to its Teichmüller part modulo `p` (`ker constantCoeff = (p)`).
  have hmem : Y - WittVector.teichmuller p (WittVector.constantCoeff Y) ∈
      Ideal.span {(p : WittVector p R)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, hteich, sub_self]
  rw [Ideal.mem_span_singleton, dvd_def] at hmem
  obtain ⟨Z, hZ⟩ := hmem
  -- Push the congruence through the quotient map.
  let π : WittVector p R →+* DSM5c.untiltOf (p := p) (W := W) R φ := DSM5c.untiltOf.mk φ
  change π Y - π (WittVector.teichmuller p (WittVector.constantCoeff Y)) ∈
      Ideal.span {((p : DSM5c.untiltOf (p := p) (W := W) R φ))}
  rw [← map_sub, hZ, map_mul, map_natCast]
  exact Ideal.mem_span_singleton.mpr ⟨π Z, rfl⟩

end UntiltOf

/-- **Step (2) of the Route U plan: Teichmüller representatives of the untilted levels.**
Every `y : lvl Q hgr N` is congruent modulo `p` to `mk (teichmuller p r)` for some
`r : lvlP Q hgr N`, namely `r` = the `0`-th Witt coordinate of any lift of `y` to
`𝕎 (lvlP Q hgr N)`.

The proof is `exists_teich_of_untiltOf` for `R := lvlP Q hgr N` and
`φ := algebraMap B♭ (lvlP Q hgr N)`: the characteristic-`p` chart level `lvlP Q hgr N` is perfect
(`chartLevel_perfect`) of characteristic `p` (`lvlP_charP`, which uses `gr 0 ≠ 0` to know that the
level is nontrivial). -/
theorem lvl_exists_teich {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    [Fact (¬ IsUnit (p : B))] [IsAdicComplete (Ideal.span {(p : B)}) B]
    (Q : DSMap.PerfectoidData p B) {gr : ℕ → B} (hgr : Work.DSM4p.IsRootSystem p gr)
    (hgr0 : gr 0 ≠ 0) (N : ℕ) (y : Work.DSM4p.lvl Q hgr N) :
    ∃ r : Work.DSM4p.lvlP Q hgr N,
      y - (Work.DSM5c.untiltOf.mk (p := p) (W := B)
            (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N))
            (WittVector.teichmuller p r)) ∈
        Ideal.span {((p : Work.DSM4p.lvl Q hgr N))} := by
  haveI hchar : CharP (Work.DSM4p.lvlP Q hgr N) p := lvlP_charP Q hgr hgr0 N
  haveI hperf : PerfectRing (Work.DSM4p.lvlP Q hgr N) p :=
    chartLevel_perfect (tiltTower_isRootSystem gr hgr)
      (tiltTower_isRootSystem Q.ϖ Q.root) N
  exact exists_teich_of_untiltOf (p := p) (W := B)
    (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N)) y

end Work.DSM4p
