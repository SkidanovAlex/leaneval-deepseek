import Mathlib

namespace Work.Resample

/-- Absorption of the five step-bounds of the chunking word into the target cost shape. -/
theorem chunkCostAbs (Kc Kd Kr V izS q : ℕ) (hq : q ≤ V) :
    Kd * (izS + 1) + Kr * 3 * (2 * izS + V + 1) + Kr * 2 * (V + izS + 1)
      + Kc * (V + (q + 1) * izS + 1) + Kr * 2 * (V + 2 * q + izS + 1)
    ≤ (1000 * (Kc + Kd + Kr) + 1000) * ((V + 1) + ((q + 1) * (izS + 1) + 1)) := by
  -- Each of the five summands is at most a small multiple of the target factor
  -- `T := (V + 1) + ((q + 1) * (izS + 1) + 1)`.
  have h1 : izS + 1 ≤ (V + 1) + ((q + 1) * (izS + 1) + 1) := by nlinarith
  have h2 : 2 * izS + V + 1 ≤ 3 * ((V + 1) + ((q + 1) * (izS + 1) + 1)) := by nlinarith
  have h3 : V + izS + 1 ≤ (V + 1) + ((q + 1) * (izS + 1) + 1) := by nlinarith
  have h4 : V + (q + 1) * izS + 1 ≤ (V + 1) + ((q + 1) * (izS + 1) + 1) := by nlinarith
  have h5 : V + 2 * q + izS + 1 ≤ 4 * ((V + 1) + ((q + 1) * (izS + 1) + 1)) := by
    nlinarith [hq]
  nlinarith [h1, h2, h3, h4, h5]

end Work.Resample
