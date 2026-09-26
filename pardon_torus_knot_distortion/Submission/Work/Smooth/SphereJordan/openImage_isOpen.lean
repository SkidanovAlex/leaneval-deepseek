import Mathlib
import Submission.Work.Smooth.SphereJordan.DiscSpansAPI
import Submission.Work.Smooth.SphereJordan.OpenImageAux

namespace Work.Smooth.SphereJordan

theorem openImage_isOpen {f : C(Work.Smooth.SphereJordan.Disc, ℂ)} (hf : Function.Injective f) :
    IsOpen (Work.Smooth.SphereJordan.openImage f) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨z, hz, rfl⟩
  rw [← mem_interior_iff_mem_nhds]
  exact mem_interior_image_of_norm_lt_one f hf z hz

end Work.Smooth.SphereJordan
