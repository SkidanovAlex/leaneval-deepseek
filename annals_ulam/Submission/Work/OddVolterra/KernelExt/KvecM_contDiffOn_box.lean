import Mathlib
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.KernelExt.Rnu_contDiff
import Submission.Work.OddVolterra.Existence.hquot_contDiff

/-!
# `C^2` regularity of the manifest odd kernel `KvecM` on a box of slopes

The paper's kernel `K₁ = J₁/√((t+H)(L_σ+L_s))` (and likewise `K₂`) is only well behaved — and
only finite — where the radicand `(t+H(s,σ))(L(σ,t)+L(s,t)) = (L(σ,t)²-L(s,t)²)/(σ-s)` of the
common denominator `Kden` is non-zero.  This file shows that, on a box of slopes
`(s,σ) ∈ [a,b]²`, the manifest representative `KvecM` of the kernel, *evaluated at the two chord
endpoints* `t = y σ` and `t = -x σ`, is `C^2` (indeed `C^∞`) as a function of `(s,σ)`, provided

* `h` is analytic (in particular smooth),
* `x`, `y` are analytic on `(0,∞)` — so that the boxes `[a,b] ⊆ (0,∞)` are inside the domain,
* `a > 0`, and
* at the two endpoints `Kden` is strictly positive on the box (the paper's standing assumption
  that the chord really cuts the profile, cf. `Work.OddVolterra.Nondegenerate`).

The proof is structural.  Every ingredient of

`KvecM n h s σ x y x' y' = ![- (K₁(-x) x' + K₁(y) y'), - (K₂(-x) x' + K₂(y) y')]`

is `C^∞` in `(s,σ)`:

* `s, σ, x σ, y σ, (deriv x) σ, (deriv y) σ` are `C^∞` on the box (the derivatives because
  `x,y` are smooth on the *open* set `(0,∞)`, hence so is `fderivWithin x (0,∞) = deriv x`);
* the numerator `J1M` (resp. `J2M`) is the manifest Bell polynomial `Rnu`, whose `C^∞`-regularity
  in the triple `(s,σ,t)` holds on *all* of `ℝ³` (`Work.OddVolterra.KernelExt.Rnu_contDiff`), so composing it
  with the smooth map `p ↦ (p.1,p.2, y p.2)` (or `p ↦ (p.1,p.2,-(x p.2))`) is free;
* the joint divided difference `hquot h s σ = ∫₀¹ h'(s+τ(σ-s))dτ` is `C^∞`
  (`Work.OddVolterra.Existence.hquot_contDiff`), so the radicand of `Kden` is `C^∞` on the box and
  strictly positive there; `Real.sqrt` is `C^∞` away from `0`, so `Kden` is `C^∞`;
* `K₁ = J₁/Kden`, `K₂ = J₂/Kden` are therefore `C^∞` on the box by the quotient rule.

The last step weakens `C^∞` to the `C^2` requested by the caller.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.KernelExt

open Work.OddVolterra

noncomputable section

/-- The derivative of a function that is `C^∞` on the open interval `(0,∞)` is again `C^∞`
there.  (`deriv` is Mathlib's total derivative; on the open set `(0,∞)` it agrees with the
derivative within the set, namely with `fderivWithin ℝ g (0,∞)`, which is what
`ContDiffOn.fderivWithin` controls.) -/
lemma contDiffOn_deriv_Ioi {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Set.Ioi 0)) :
    ContDiffOn ℝ ∞ (deriv g) (Set.Ioi 0) := by
  have hfd : ContDiffOn ℝ ∞ (fderivWithin ℝ g (Set.Ioi 0)) (Set.Ioi 0) :=
    hg.fderivWithin (uniqueDiffOn_Ioi 0) le_rfl
  have hfd2 : ContDiffOn ℝ ∞ (fun σ => (fderivWithin ℝ g (Set.Ioi 0) σ) (1 : ℝ)) (Set.Ioi 0) :=
    hfd.clm_apply contDiffOn_const
  refine hfd2.congr (fun σ hσ => ?_)
  show deriv g σ = (fderivWithin ℝ g (Set.Ioi 0) σ) 1
  rw [fderivWithin_of_isOpen isOpen_Ioi hσ]
  rfl

/-- The composition of the Bell numerator `Rnu ν h init m` with a `C^∞` "third coordinate"
`t` is `C^∞` on any set. -/
lemma contDiffOn_Rnu_comp (ν : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {init : ℝ × ℝ × ℝ → ℝ} (hinit : ContDiff ℝ (⊤ : ℕ∞) init) (m : ℕ)
    {B : Set (ℝ × ℝ)} {t : ℝ × ℝ → ℝ} (ht : ContDiffOn ℝ ∞ t B) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Rnu ν h init m (p.1, p.2, t p)) B := by
  have hPhi : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (p.1, (p.2, t p))) B :=
    contDiffOn_fst.prodMk (contDiffOn_snd.prodMk ht)
  have hR : ContDiffOn ℝ ∞ (Rnu ν h init m) Set.univ :=
    ((Work.OddVolterra.KernelExt.Rnu_contDiff ν hh hinit m).contDiffOn :
      ContDiffOn ℝ (⊤ : ℕ∞) (Rnu ν h init m) Set.univ).of_le le_rfl
  have hcomp : ContDiffOn ℝ ∞ (Rnu ν h init m ∘ fun p : ℝ × ℝ => (p.1, (p.2, t p))) B :=
    hR.comp hPhi (fun _ _ => trivial)
  exact hcomp.congr (fun p _ => rfl)

/-- `Kden h s σ (t p)` is `C^∞` in `p` on `B`, as soon as the third coordinate `t` is, and the
radicand — hence `Kden` itself — is positive on `B`. -/
lemma contDiffOn_Kden_comp {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {B : Set (ℝ × ℝ)} {t : ℝ × ℝ → ℝ} (ht : ContDiffOn ℝ ∞ t B)
    (htpos : ∀ p ∈ B, 0 < Kden h p.1 p.2 (t p)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Kden h p.1 p.2 (t p)) B := by
  have hquotB : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => hquot h p.1 p.2) B :=
    (Work.OddVolterra.Existence.hquot_contDiff hh).contDiffOn
  have hhB1 : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => h p.1) B :=
    (hh.contDiffOn : ContDiffOn ℝ ∞ h Set.univ).comp contDiffOn_fst (fun _ _ => trivial)
  have hhB2 : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => h p.2) B :=
    (hh.contDiffOn : ContDiffOn ℝ ∞ h Set.univ).comp contDiffOn_snd (fun _ _ => trivial)
  have hrad : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      (t p + hquot h p.1 p.2) * ((p.2 * t p + h p.2) + (p.1 * t p + h p.1))) B :=
    (ht.add hquotB).mul (((contDiffOn_snd.mul ht).add hhB2).add
      ((contDiffOn_fst.mul ht).add hhB1))
  have hsqrt := hrad.sqrt (fun p hp => by
    have h := htpos p hp
    rw [Kden, Real.sqrt_pos, line, line] at h
    exact ne_of_gt h)
  simpa only [Kden, line] using hsqrt

/-- The first manifest kernel `K₁`, evaluated at a `C^∞` family of third coordinates `t`, is
`C^∞` on the box where `Kden` is positive. -/
lemma contDiffOn_K1M_comp (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {B : Set (ℝ × ℝ)} {t : ℝ × ℝ → ℝ} (ht : ContDiffOn ℝ ∞ t B)
    (htpos : ∀ p ∈ B, 0 < Kden h p.1 p.2 (t p)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => K1M n h p.1 p.2 (t p)) B := by
  have hJ : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => J1M n h p.1 p.2 (t p)) B := by
    have h := contDiffOn_Rnu_comp ((n : ℝ) + 1 / 2) hh (init := fun _ => (1 : ℝ))
      contDiff_const (n + 1) ht
    simpa only [J1M] using h
  have hKd := contDiffOn_Kden_comp (hh.of_le le_rfl) ht htpos
  exact hJ.div hKd (fun p hp => ne_of_gt (htpos p hp))

/-- The second manifest kernel `K₂`, evaluated at a `C^∞` family of third coordinates `t`, is
`C^∞` on the box where `Kden` is positive. -/
lemma contDiffOn_K2M_comp (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {B : Set (ℝ × ℝ)} {t : ℝ × ℝ → ℝ} (ht : ContDiffOn ℝ ∞ t B)
    (htpos : ∀ p ∈ B, 0 < Kden h p.1 p.2 (t p)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => K2M n h p.1 p.2 (t p)) B := by
  have hinit : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ × ℝ => lineSlope h q.1 q.2.2) := by
    unfold lineSlope
    fun_prop
  have hJ : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => J2M n h p.1 p.2 (t p)) B := by
    have h := contDiffOn_Rnu_comp ((n : ℝ) - 1 / 2) hh hinit n ht
    simpa only [J2M] using h
  have hKd := contDiffOn_Kden_comp (hh.of_le le_rfl) ht htpos
  exact hJ.div hKd (fun p hp => ne_of_gt (htpos p hp))

/-- **The manifest odd kernel is `C²` on a box of slopes.**  With `h` analytic and `x`, `y`
analytic on `(0,∞)`, and the two chord-endpoint radicands positive on `[a,b]²` (`a > 0`), the
kernel `KvecM`, evaluated at `t = y σ` and `t = -x σ` together with the derivatives of `x,y`, is
`C²` (in fact `C^∞`) as a function of the slope pair `(s,σ) ∈ [a,b]²`. -/
theorem KvecM_contDiffOn_box (n : ℕ) {h x y : ℝ → ℝ} {a b : ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hx : ContDiffOn ℝ (⊤ : ℕ∞) x (Set.Ioi 0)) (hy : ContDiffOn ℝ (⊤ : ℕ∞) y (Set.Ioi 0))
    (ha : 0 < a) (hb : b ≤ 1)
    (hposy : ∀ s σ : ℝ, s ∈ Set.Icc a b → σ ∈ Set.Icc a b → 0 < Work.OddVolterra.Kden h s σ (y σ))
    (hposx : ∀ s σ : ℝ, s ∈ Set.Icc a b → σ ∈ Set.Icc a b → 0 < Work.OddVolterra.Kden h s σ (-(x σ))) :
    ContDiffOn ℝ 2
      (fun p : ℝ × ℝ => Work.OddVolterra.KernelExt.KvecM n h p.1 p.2
        (x p.2) (y p.2) (deriv x p.2) (deriv y p.2))
      (Set.Icc a b ×ˢ Set.Icc a b) := by
  have hx_smooth : ContDiffOn ℝ ∞ x (Set.Ioi 0) := hx.of_le le_rfl
  have hy_smooth : ContDiffOn ℝ ∞ y (Set.Ioi 0) := hy.of_le le_rfl
  have hmaps : MapsTo (fun p : ℝ × ℝ => p.2) (Set.Icc a b ×ˢ Set.Icc a b) (Set.Ioi 0) :=
    fun p hp => lt_of_lt_of_le ha hp.2.1
  have hxB : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => x p.2) (Set.Icc a b ×ˢ Set.Icc a b) :=
    hx_smooth.comp contDiffOn_snd hmaps
  have hyB : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => y p.2) (Set.Icc a b ×ˢ Set.Icc a b) :=
    hy_smooth.comp contDiffOn_snd hmaps
  have hdxB : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => deriv x p.2) (Set.Icc a b ×ˢ Set.Icc a b) :=
    (contDiffOn_deriv_Ioi hx_smooth).comp contDiffOn_snd hmaps
  have hdyB : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => deriv y p.2) (Set.Icc a b ×ˢ Set.Icc a b) :=
    (contDiffOn_deriv_Ioi hy_smooth).comp contDiffOn_snd hmaps
  have hK1x : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => K1M n h p.1 p.2 (-(x p.2)))
      (Set.Icc a b ×ˢ Set.Icc a b) :=
    contDiffOn_K1M_comp n hh hxB.neg (fun p hp => hposx p.1 p.2 hp.1 hp.2)
  have hK1y : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => K1M n h p.1 p.2 (y p.2))
      (Set.Icc a b ×ˢ Set.Icc a b) :=
    contDiffOn_K1M_comp n hh hyB (fun p hp => hposy p.1 p.2 hp.1 hp.2)
  have hK2x : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => K2M n h p.1 p.2 (-(x p.2)))
      (Set.Icc a b ×ˢ Set.Icc a b) :=
    contDiffOn_K2M_comp n hh hxB.neg (fun p hp => hposx p.1 p.2 hp.1 hp.2)
  have hK2y : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => K2M n h p.1 p.2 (y p.2))
      (Set.Icc a b ×ˢ Set.Icc a b) :=
    contDiffOn_K2M_comp n hh hyB (fun p hp => hposy p.1 p.2 hp.1 hp.2)
  have hgoal : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => KvecM n h p.1 p.2
      (x p.2) (y p.2) (deriv x p.2) (deriv y p.2)) (Set.Icc a b ×ˢ Set.Icc a b) := by
    rw [contDiffOn_pi]
    intro i
    fin_cases i
    · simpa [KvecM] using ((hK1x.mul hdxB).add (hK1y.mul hdyB)).neg
    · simpa [KvecM] using ((hK2x.mul hdxB).add (hK2y.mul hdyB)).neg
  exact hgoal.of_le (WithTop.coe_le_coe.mpr le_top)

end

end Work.OddVolterra.KernelExt
