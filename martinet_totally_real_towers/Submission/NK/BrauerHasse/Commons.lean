/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Re-exports of the commons used by the Brauer/local-global chapter

This module only re-exports the parts of `Submission/Commons/` and of the Neukirch–Uchida
development that the lemmas of `Submission/Work/BrauerHasse/` are stated against, so that those
lemmas can be delegated with a single `depends_on` entry.

* `IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime` and
  `exists_heightOneSpectrum_eq_valuationSubringAtPrime` — the finite places of a number field as
  valuation subrings;
* `NumberField.RingOfIntegers` and `ringOfIntegers_le_valuationSubring`;
* `Submission.NeukirchUchida.Local.PlaceFromValuation` — `placeOf`, `decompositionSubgroup`, and
  the identification of the stabiliser of a valuation subring with a decomposition group.
-/

import Submission.Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
import Submission.Commons.NumberTheory.NumberField.ringOfIntegers_le_valuationSubring
import Submission.NeukirchUchida.Local.PlaceFromValuation

set_option autoImplicit false
