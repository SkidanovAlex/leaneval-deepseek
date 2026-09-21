import Mathlib
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.KernelExt.KvecM_contDiffOn_box
import Submission.Work.OddVolterra.Existence.hquot_contDiff

/-!
# `C^∞` regularity of the manifest odd kernel under composition with a parameter map

`Work.OddVolterra.KernelExt.KvecM_contDiffOn_box` shows that the manifest odd kernel

`KvecM n h s σ x y x' y' = ![- (K₁(s,σ,-x) x' + K₁(s,σ,y) y'),
                              - (K₂(s,σ,-x) x' + K₂(s,σ,y) y')]`

is smooth as a function of the slope pair `(s,σ)` **on a box** `[a,b]²`, when the
remaining four arguments are themselves the smooth functions `x σ, y σ, (deriv x) σ, (deriv y) σ`.
For the Volterra fixed-point argument one needs the same statement in a more flexible form: the
six real arguments of `KvecM` are arbitrary `C^∞` functions on an arbitrary subset `B` of a
normed space `W`, and the conclusion is `ContDiffOn` on `B`.  This file supplies exactly that,
by composing the manifest numerator (a Bell polynomial, smooth on *all* of `ℝ³`, see
`Rnu_contDiff`) and the manifest denominator `Kden` (smooth wherever its radicand is non-zero)
with the parameter map.

The positivity hypotheses `0 < Kden h (a p) (s p) (-(x p))` and `0 < Kden h (a p) (s p) (y p)`
are the paper's standing assumption that the chord really cuts the profile: they make the two
`Kden`-factors non-zero, so that the divisions defining `K₁`,`K₂` are legitimate.

The first four lemmas are the general (`W`-valued, `ContDiffOn`-set) forms of the corresponding
`KvecM_contDiffOn_box` lemmas; the last statement is the requested composition theorem.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.KernelExt

open Work.OddVolterra

noncomputable section

/-- The `∂_s L` initial datum `q ↦ lineSlope h q.1 q.2.2` of the second Bell numerator is
smooth when `h` is. -/
lemma contDiff_lineSlope_init {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => lineSlope h q.1 q.2.2) := by
  unfold lineSlope
  fun_prop

/-- The first manifest numerator `J1M`, evaluated at `C^∞` parameter functions `α, σ, t`, is
`C^∞` on `B`.  (The numerator is a Bell polynomial in the triple `(s,σ,t)`, hence smooth on all
of `ℝ³`; no positivity is needed.) -/
lemma contDiffOn_J1M_comp_gen {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {B : Set W} {α σ t : W → ℝ}
    (hα : ContDiffOn ℝ ∞ α B) (hσ : ContDiffOn ℝ ∞ σ B) (ht : ContDiffOn ℝ ∞ t B) :
    ContDiffOn ℝ ∞ (fun p : W => J1M n h (α p) (σ p) (t p)) B := by
  have hPhi : ContDiffOn ℝ ∞ (fun p : W => (α p, (σ p, t p))) B :=
    hα.prodMk (hσ.prodMk ht)
  have hR : ContDiffOn ℝ ∞ (Rnu ((n : ℝ) + 1 / 2) h (fun _ => (1 : ℝ)) (n + 1)) Set.univ :=
    ((Rnu_contDiff ((n : ℝ) + 1 / 2) hh contDiff_const (n + 1)).contDiffOn :
      ContDiffOn ℝ (⊤ : ℕ∞) _ Set.univ).of_le le_rfl
  have h := hR.comp hPhi (fun _ _ => trivial)
  simpa only [J1M, Function.comp_def] using h

/-- The second manifest numerator `J2M`, evaluated at `C^∞` parameter functions `α, σ, t`, is
`C^∞` on `B`. -/
lemma contDiffOn_J2M_comp_gen {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {B : Set W} {α σ t : W → ℝ}
    (hα : ContDiffOn ℝ ∞ α B) (hσ : ContDiffOn ℝ ∞ σ B) (ht : ContDiffOn ℝ ∞ t B) :
    ContDiffOn ℝ ∞ (fun p : W => J2M n h (α p) (σ p) (t p)) B := by
  have hPhi : ContDiffOn ℝ ∞ (fun p : W => (α p, (σ p, t p))) B :=
    hα.prodMk (hσ.prodMk ht)
  have hR : ContDiffOn ℝ ∞ (Rnu ((n : ℝ) - 1 / 2) h
      (fun q : ℝ × ℝ × ℝ => lineSlope h q.1 q.2.2) n) Set.univ :=
    ((Rnu_contDiff ((n : ℝ) - 1 / 2) hh (contDiff_lineSlope_init hh) n).contDiffOn :
      ContDiffOn ℝ (⊤ : ℕ∞) _ Set.univ).of_le le_rfl
  have h := hR.comp hPhi (fun _ _ => trivial)
  simpa only [J2M, Function.comp_def] using h

/-- The manifest denominator `Kden`, evaluated at `C^∞` parameter functions `α, σ, t`, is `C^∞`
on `B` wherever its radicand is positive (so that `Real.sqrt` is smooth there). -/
lemma contDiffOn_Kden_comp_gen {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {B : Set W} {α σ t : W → ℝ}
    (hα : ContDiffOn ℝ ∞ α B) (hσ : ContDiffOn ℝ ∞ σ B) (ht : ContDiffOn ℝ ∞ t B)
    (hpos : ∀ p ∈ B, 0 < Kden h (α p) (σ p) (t p)) :
    ContDiffOn ℝ ∞ (fun p : W => Kden h (α p) (σ p) (t p)) B := by
  have hq : ContDiffOn ℝ ∞ (fun p : W => hquot h (α p) (σ p)) B :=
    ((Work.OddVolterra.Existence.hquot_contDiff hh).contDiffOn (s := Set.univ)).comp
      (hα.prodMk hσ) (fun _ _ => trivial)
  have hhα : ContDiffOn ℝ ∞ (fun p : W => h (α p)) B :=
    (hh.contDiffOn (s := Set.univ)).comp hα (fun _ _ => trivial)
  have hhσ : ContDiffOn ℝ ∞ (fun p : W => h (σ p)) B :=
    (hh.contDiffOn (s := Set.univ)).comp hσ (fun _ _ => trivial)
  have hrad : ContDiffOn ℝ ∞ (fun p : W =>
      (t p + hquot h (α p) (σ p)) * ((σ p * t p + h (σ p)) + (α p * t p + h (α p)))) B :=
    (ht.add hq).mul (((hσ.mul ht).add hhσ).add ((hα.mul ht).add hhα))
  have hsqrt := hrad.sqrt (fun p hp => by
    have h := hpos p hp
    rw [Kden, Real.sqrt_pos, line, line] at h
    exact ne_of_gt h)
  simpa only [Kden, line] using hsqrt

/-- The first manifest kernel `K₁ = J1M/Kden`, evaluated at `C^∞` parameter functions `α, σ, t`,
is `C^∞` on `B` where `Kden` is positive. -/
lemma contDiffOn_K1M_comp_gen {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {B : Set W} {α σ t : W → ℝ}
    (hα : ContDiffOn ℝ ∞ α B) (hσ : ContDiffOn ℝ ∞ σ B) (ht : ContDiffOn ℝ ∞ t B)
    (hpos : ∀ p ∈ B, 0 < Kden h (α p) (σ p) (t p)) :
    ContDiffOn ℝ ∞ (fun p : W => K1M n h (α p) (σ p) (t p)) B :=
  (contDiffOn_J1M_comp_gen n hh hα hσ ht).div
    (contDiffOn_Kden_comp_gen hh hα hσ ht hpos) (fun p hp => ne_of_gt (hpos p hp))

/-- The second manifest kernel `K₂ = J2M/Kden`, evaluated at `C^∞` parameter functions
`α, σ, t`, is `C^∞` on `B` where `Kden` is positive. -/
lemma contDiffOn_K2M_comp_gen {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {B : Set W} {α σ t : W → ℝ}
    (hα : ContDiffOn ℝ ∞ α B) (hσ : ContDiffOn ℝ ∞ σ B) (ht : ContDiffOn ℝ ∞ t B)
    (hpos : ∀ p ∈ B, 0 < Kden h (α p) (σ p) (t p)) :
    ContDiffOn ℝ ∞ (fun p : W => K2M n h (α p) (σ p) (t p)) B :=
  (contDiffOn_J2M_comp_gen n hh hα hσ ht).div
    (contDiffOn_Kden_comp_gen hh hα hσ ht hpos) (fun p hp => ne_of_gt (hpos p hp))

/-- **The manifest odd kernel is `C^∞` on `B` under composition with a `C^∞` parameter map.**
The six real arguments `a, s, x, y, x', y'` of `KvecM n h` are `C^∞` functions on `B ⊆ W`, and
the two `Kden`-radicands at the chord endpoints `-(x p)` and `y p` are positive on `B`; then
`p ↦ KvecM n h (a p) (s p) (x p) (y p) (x' p) (y' p)` is `C^∞` on `B`. -/
theorem KvecM_contDiffOn_comp {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {B : Set W} {a s x y x' y' : W → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a B) (hs : ContDiffOn ℝ (⊤ : ℕ∞) s B)
    (hx : ContDiffOn ℝ (⊤ : ℕ∞) x B) (hy : ContDiffOn ℝ (⊤ : ℕ∞) y B)
    (hx' : ContDiffOn ℝ (⊤ : ℕ∞) x' B) (hy' : ContDiffOn ℝ (⊤ : ℕ∞) y' B)
    (hposx : ∀ p ∈ B, 0 < Work.OddVolterra.Kden h (a p) (s p) (-(x p)))
    (hposy : ∀ p ∈ B, 0 < Work.OddVolterra.Kden h (a p) (s p) (y p)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : W => Work.OddVolterra.KernelExt.KvecM n h (a p) (s p) (x p) (y p) (x' p) (y' p)) B := by
  have hK1x : ContDiffOn ℝ ∞ (fun p : W => K1M n h (a p) (s p) (-(x p))) B :=
    contDiffOn_K1M_comp_gen n hh ha hs hx.neg (fun p hp => hposx p hp)
  have hK1y : ContDiffOn ℝ ∞ (fun p : W => K1M n h (a p) (s p) (y p)) B :=
    contDiffOn_K1M_comp_gen n hh ha hs hy (fun p hp => hposy p hp)
  have hK2x : ContDiffOn ℝ ∞ (fun p : W => K2M n h (a p) (s p) (-(x p))) B :=
    contDiffOn_K2M_comp_gen n hh ha hs hx.neg (fun p hp => hposx p hp)
  have hK2y : ContDiffOn ℝ ∞ (fun p : W => K2M n h (a p) (s p) (y p)) B :=
    contDiffOn_K2M_comp_gen n hh ha hs hy (fun p hp => hposy p hp)
  rw [contDiffOn_pi]
  intro i
  fin_cases i
  · simpa [KvecM] using ((hK1x.mul hx').add (hK1y.mul hy')).neg
  · simpa [KvecM] using ((hK2x.mul hx').add (hK2y.mul hy')).neg

end

end Work.OddVolterra.KernelExt
