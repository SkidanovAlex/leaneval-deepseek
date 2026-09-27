import Mathlib

namespace Work.Drive

open Filter Topology

/-- The identity `n a * n (a+b) + n (-a) * n b + n (-(a+b)) * n (-b) = 1`, known on a dense subset
of the triples `(a,b)` with `a, b, a+b ∈ Z`, extends to all such triples, because it is locally
constant there: at a valid triple each of the six arguments `a`, `a+b`, `-a`, `b`, `-(a+b)`, `-b`
lies in `Z`, and `n` is locally constant on `Z`. -/
theorem identity_of_dense_localconst
    (Z : Set UnitAddCircle) (hneg : ∀ u ∈ Z, -u ∈ Z)
    (n : UnitAddCircle → ZMod 2)
    (hnloc : ∀ x ∈ Z, ∀ᶠ y in nhds x, y ∈ Z → n y = n x)
    (G : Set (UnitAddCircle × UnitAddCircle))
    (hdense : ∀ a b : UnitAddCircle, a ∈ Z → b ∈ Z → a + b ∈ Z →
      (a, b) ∈ closure (G ∩ {q : UnitAddCircle × UnitAddCircle |
        q.1 ∈ Z ∧ q.2 ∈ Z ∧ q.1 + q.2 ∈ Z}))
    (hid : ∀ q ∈ G, q.1 ∈ Z → q.2 ∈ Z → q.1 + q.2 ∈ Z →
      n q.1 * n (q.1 + q.2) + n (-q.1) * n q.2 + n (-(q.1 + q.2)) * n (-q.2) = 1) :
    ∀ a b : UnitAddCircle, a ∈ Z → b ∈ Z → a + b ∈ Z →
      n a * n (a + b) + n (-a) * n b + n (-(a + b)) * n (-b) = 1 := by
  intro a b ha hb hab
  -- local constancy of the six factors at the triple `(a, b)`
  have h1 : ∀ᶠ q : UnitAddCircle × UnitAddCircle in 𝓝 (a, b), q.1 ∈ Z → n q.1 = n a :=
    (continuous_fst.tendsto (a, b)).eventually (hnloc a ha)
  have h2 : ∀ᶠ q : UnitAddCircle × UnitAddCircle in 𝓝 (a, b),
      q.1 + q.2 ∈ Z → n (q.1 + q.2) = n (a + b) :=
    ((continuous_fst.add continuous_snd).tendsto (a, b)).eventually (hnloc (a + b) hab)
  have h3 : ∀ᶠ q : UnitAddCircle × UnitAddCircle in 𝓝 (a, b), -q.1 ∈ Z → n (-q.1) = n (-a) :=
    (continuous_fst.neg.tendsto (a, b)).eventually (hnloc (-a) (hneg a ha))
  have h4 : ∀ᶠ q : UnitAddCircle × UnitAddCircle in 𝓝 (a, b), q.2 ∈ Z → n q.2 = n b :=
    (continuous_snd.tendsto (a, b)).eventually (hnloc b hb)
  have h5 : ∀ᶠ q : UnitAddCircle × UnitAddCircle in 𝓝 (a, b),
      -(q.1 + q.2) ∈ Z → n (-(q.1 + q.2)) = n (-(a + b)) :=
    ((continuous_fst.add continuous_snd).neg.tendsto (a, b)).eventually
      (hnloc (-(a + b)) (hneg (a + b) hab))
  have h6 : ∀ᶠ q : UnitAddCircle × UnitAddCircle in 𝓝 (a, b), -q.2 ∈ Z → n (-q.2) = n (-b) :=
    (continuous_snd.neg.tendsto (a, b)).eventually (hnloc (-b) (hneg b hb))
  have hloc : ∀ᶠ q : UnitAddCircle × UnitAddCircle in 𝓝 (a, b),
      q ∈ {q : UnitAddCircle × UnitAddCircle | q.1 ∈ Z ∧ q.2 ∈ Z ∧ q.1 + q.2 ∈ Z} →
        n q.1 * n (q.1 + q.2) + n (-q.1) * n q.2 + n (-(q.1 + q.2)) * n (-q.2)
          = n a * n (a + b) + n (-a) * n b + n (-(a + b)) * n (-b) := by
    filter_upwards [h1, h2, h3, h4, h5, h6] with q h1q h2q h3q h4q h5q h6q hqS
    obtain ⟨hq1, hq2, hq3⟩ := hqS
    rw [h1q hq1, h2q hq3, h3q (hneg q.1 hq1), h4q hq2, h5q (hneg (q.1 + q.2) hq3),
      h6q (hneg q.2 hq2)]
  -- density: the triple `(a,b)` is a limit of valid elements of `G`
  have hfr : ∃ᶠ q in 𝓝 (a, b),
      q ∈ G ∩ {q : UnitAddCircle × UnitAddCircle | q.1 ∈ Z ∧ q.2 ∈ Z ∧ q.1 + q.2 ∈ Z} :=
    mem_closure_iff_frequently.mp (hdense a b ha hb hab)
  obtain ⟨q, hqGS, hqloc⟩ := (hfr.and_eventually hloc).exists
  obtain ⟨hqG, hqS⟩ := hqGS
  obtain ⟨hq1, hq2, hq3⟩ := hqS
  rw [← hqloc ⟨hq1, hq2, hq3⟩]
  exact hid q hqG hq1 hq2 hq3

end Work.Drive
