import Mathlib.RingTheory.PowerSeries.Inverse

namespace Commons.RingTheory.PowerSeries

theorem isUnit_iff_constantCoeff {R : Type*} [CommRing R] (f : PowerSeries R) : IsUnit f ↔ IsUnit (PowerSeries.constantCoeff f) :=
  _root_.PowerSeries.isUnit_iff_constantCoeff

end Commons.RingTheory.PowerSeries