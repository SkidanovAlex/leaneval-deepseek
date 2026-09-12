import Mathlib
import Submission.FeketeLim
import Submission.MaximalityOne
import Submission.Step3Defs
import Submission.ModelStarKKM

/-!
# Step 3 -- Dubinin's symmetric-maximality (statement file + first cases)

STEP-3 CORE (DEEP -- Dubinin's theorem): among all hedgehogs made of `s`
segments of length at most `L` through the origin (in arbitrary distinct
directions), the Fekete root limsup is maximized by the rotationally
symmetric equal-angle s-star; the maximum value is `L·4^(-1/s)`:

    sym_maximality :  for any s unit directions u_0,…,u_{s−1} (pairwise
    distinct) and K := ⋃_j [0, L·u_j] (each spike of length L):
        limsup_n (feketeNumber K (n+1))^(2/((n+1)·n)) ≤ L·4^(-1/s).

Together with the lengthening reduction (DubininMap: m_n(star S) ≤
m_n(starL S L)) and the symmetric value (step 4: limsup of the symmetric
star = L·4^(-1/s)), this yields dubinin_fekete_limsup.

DECOMPOSITION (candidate routes; both research-scale, NO elementary route
known after many sessions):
  (i)  Symmetrization (Dubinin): spreading the directions apart (moving
       towards equal angles, keeping the spikes on a circle of directions)
       cannot decrease the Fekete root limsup.  The discrete "spreading
       move": replacing two directions by directions farther apart (in the
       cyclic order) increases capacity.  Needs a polarization/
       symmetrization lemma for Fekete products -- not in Mathlib.
  (ii) Eremenko/KL: a cap-1 s-spike hedgehog is the image of the exterior
       unit disk under F(z) = ∏_j ((z − z_j)(z^{-1} − z̄_j))^{r_j}
       (Σ r_j = 1), with the spike lengths |a_j| = max over the arc j of
       ∏_k |z − z_k|^{2 r_k}; the verified Konyagin-Lev circle inequality
       (Submission.KLMain.koniagin_lev_circle: n unit points z_k, weights
       p_k ≥ 0, Σp_k = n ⟹ ∃ unit w: ∏_k |w − z_k|^{p_k} ≥ 2) then gives
       max_j |a_j| ≥ 4^(1/s) for cap-1 stars, i.e. cap ≤ 4^(-1/s)·max
       length.  Needs conformal-map machinery (absent from Mathlib).

FIRST CASE (PROVED): s = 1.  `sym_maximality_one` (a single spike of
length ≤ L has Fekete root limsup ≤ L/4 = L·4^(-1/1)) is proved via
`Submission.MaximalityOne.maximality_one` (monotonicity in the segment
length + the segment asymptotic `hseg` supplied by
Submission.SegmentAsymptotic, child L79; the s = 1 piece is closed).

MAIN STATEMENT (DEEP, the single remaining sorry of the E1 chain):
`sym_maximality` below -- any s-spike hedgehog of spikes of equal length
L has Fekete root limsup at most L·4^(-1/s).  This is Dubinin's theorem
for hedgehogs (capacity ≤ 4^(-1/s)·max length); every other step of the
E1 reduction chain (SS1/SS2/SS3/Dubinin.lean/E1Content) is verified and
depends only on this one statement (see Submission/STATUS.md session-46
header for the full reduction map).
-/

noncomputable section

open scoped Real Polynomial Topology BigOperators

namespace Submission.Step3

open Filter


/-- **Step-3 core (DEEP).**  Any hedgehog of `s` spikes of length `L` has
Fekete root limsup at most `L·4^(-1/s)`.  (`s := u.card`.) -/
theorem sym_maximality (u : Finset ℂ) (hu : ∀ w ∈ u, ‖w‖ = 1)
    (hs : 1 ≤ u.card) {L : ℝ} (hL : 0 ≤ L) :
    Filter.limsup (fun n : ℕ =>
        (Submission.FeketeLim.feketeNumber (dirStar u L) (n + 1)) ^
          (2 / (((n + 1 : ℝ)) * (n : ℝ)))) Filter.atTop
      ≤ (L : ℝ) * (4 : ℝ) ^ (-1 / (u.card : ℝ)) := by
  exact Submission.ModelStarKKM.sym_maximality u hu hs hL

/-- **s = 1 case (provable).**  A single spike of length at most `L` has
Fekete root limsup at most `L/4`.  (`hseg` supplies the segment limsup
value ℓ/4 for each segment length ℓ; monotonicity in the length gives
`≤ L/4`.) -/
theorem sym_maximality_one (L : ℝ) (hL : 0 ≤ L)
    (hseg : ∀ M : ℝ, 0 ≤ M →
      Filter.limsup (fun n : ℕ =>
        (Submission.FeketeLim.feketeNumber (segment ℝ 0 (M : ℂ)) (n + 1)) ^
          (2 / (((n + 1 : ℝ)) * (n : ℝ)))) Filter.atTop = M / 4) :
    Filter.limsup (fun n : ℕ =>
      (Submission.FeketeLim.feketeNumber (segment ℝ 0 (L : ℂ)) (n + 1)) ^
        (2 / (((n + 1 : ℝ)) * (n : ℝ)))) Filter.atTop
    ≤ L / 4 := by
  exact Submission.MaximalityOne.maximality_one (ell := L) (hell := hL) (hL := hL)
    (helle := le_rfl) hseg

end Submission.Step3

end
