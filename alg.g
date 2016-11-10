##############################################################
#
# This function expresses mP as a summand of A^n and computes
# the complement
#
# Return values: [n, mPs, in_multiplicities, ou_multiplicities]
# n = the minimal n such that mP embeds to A^n
# mPs = a complement of mP in A^n
# in_multiplicities[i] = the multiplicity of e_iA inside mP
# ou_multiplicities[i] = the multiplicity of e_iA inside mPs
#
# Remark: The use of CommonDirectSummand() in the implementation
# of the function seems to be an overkill
#
##############################################################

SuppProjModule := function(mP)
  local A, PP, mPs, n, common, i, j, diff,
        in_multiplicities, ou_multiplicities;

  A := RightActingAlgebra(mP);
  PP:= IndecProjectiveModules(A);
  in_multiplicities := [];
  ou_multiplicities := [];
  n := 0;

  # Go through all modules of the form e_iA.
  for i in [1..Length(PP)] do
    Add(in_multiplicities, 0);

    # Trying how many times is given e_iA contained in P as a summand.
    repeat
      common := CommonDirectSummand(mP, PP[i]);
      if IsList(common) then
        in_multiplicities[i] := in_multiplicities[i] + 1;
        mP := common[2];
      fi;
    until IsList(common) = false;

    n := Maximum([n, in_multiplicities[i]]);
  od;

  # Computin P'.
  mPs := [];
  for i in [1..Length(PP)] do
    diff := n - in_multiplicities[i];
    ou_multiplicities[i] := diff;

    for j in [1..diff] do
      Add(mPs, PP[i]);
    od;
  od;
  mPs := DirectSumOfModules(mPs);

  return [n, mPs, in_multiplicities, ou_multiplicities];
end;

##############################################################
#
# An auxiliary function to travel between a representation
# and its projective presentation. It returns a list
# of bases of indecomposable projectives as elements of
# the *algebra*. 
#
# The rest of the algoritm seems to depend on the fact that
# the projectives come in the same order as in the output from
# IndecProjectiveModules(), and that the bases returned by
# BasisOfProjectives() are the same as those returend by
# Basis() applied to the projectives given
# by IndecProjectiveModules().
#
##############################################################

ProjectiveBasisVectorGens := function(PP)
  local A;

  A := RightActingAlgebra(PP[1]);

  return List(BasisOfProjectives(A), b -> Flat(b));
end;

##############################################################
#
# Another auxiliary function: Given the matrix of an A-linear
# map mM -> mN with respect to the standard bases of mM, mN
# as representations, it transforms it to an input
# of RightModuleHomOverAlgebra() (that is, it returns the list
# of blocks of the necessarily block diagonal matrix).
#
##############################################################

ExtractHomMatrices := function(matrix, mM, mN)
  local A, Q, d_mM, d_mN, used_x, used_y, i, j, k, dx, dy,
    matrices;

  A := RightActingAlgebra(mM);
  Q := QuiverOfPathAlgebra(A);

  matrices := [];
  d_mM := DimensionVector(mM);
  d_mN := DimensionVector(mN);
  used_x := 0;
  used_y := 0;
  for i in [1..NumberOfVertices(Q)] do
    dx := d_mN[i];
    dy := d_mM[i];

    matrices[i] := [];

    if dy = 0 and dx = 0 then
      Add(matrices[i], [0]);
    elif dy = 0 then
      Add(matrices[i], List([1..dx], j -> 0));
    elif dx = 0 then
      Add(matrices[i], List([1..dy], j -> [0]));
    else
      for j in [1+used_y..dy+used_y] do
        Add(matrices[i], List([1+used_x..dx+used_x], k -> matrix[j][k]));
      od;
    fi;

    used_x := used_x + dx;
    used_y := used_y + dy;
  od;

  return matrices;
end;

##############################################################
#
# The translation between elemets of Hom(P,A) as homomorphisms
# and of P^* as a representation.
#
# It assumes that we are given a homomorphism f: P --> A where
# P is a direct sum of indecomposable projectives and
# a representation mP_star over the opposite algebra which is
# the sum of the corresponding projective from the other side
# (in the same order), and it realizes an isomorphism
# Hom(P,A) \cong mP_star of left A-modules.
#
# The function seems to assume (from the context where it is
# called) that the output of ProjectiveCover() is constructed
# so that all summands of the type e_1A come first, then all
# modules of type e_2A come, and so on.
#
##############################################################

FromHomToProjRep := function(f, mP_star)
  local i, j, incl, incl2, proj, mu, mu_f, pi, mu2,
    A, e_i, e_i_op, fe_i, result, mP, me_iA, PP, mA,
    as_algebra_element, lambda, lambda_op, pi_f_ei, coeffs;

  mP := Source(f);
  mA := Range(f);
  A := RightActingAlgebra(mP);

  # Modules e_iA.
  PP := IndecProjectiveModules(A);

  incl := DirectSumInclusions(mP);
  incl2:= DirectSumInclusions(mP_star);
  proj := DirectSumProjections(mA);
  as_algebra_element := ProjectiveBasisVectorGens(PP);

  result := Zero(mP_star);

  # For all inclusions from direct summands of P, i.e. the modules e_iA
  for i in [1..Length(incl)] do
    # We compose the inclusion to the morphism e_iA --> P -> A.
    mu := incl[i];
    mu_f := mu * f;

    # We compute e_iA a e_i.
    me_iA := Source(mu_f);
    e_i := MinimalGeneratingSetOfModule(me_iA)[1];

    # We map e_i using the homomorphism f.
    fe_i := ImageElm(mu_f, e_i);

    # Now we are going to project f(e_i) to the modules e_iA
    # ... to each such image we find the corresponding element ...
    # ... of the algebra A and we sum the results.
    lambda := Zero(A);
    for j in [1..Length(proj)] do
      pi := proj[j];
      pi_f_ei := ImageElm(pi, fe_i);
      coeffs  := Coefficients(Basis(PP[j]), pi_f_ei);
      lambda  := lambda + coeffs * as_algebra_element[j];
    od;

    # We compute the opposite element.
    lambda_op := OppositePathAlgebraElement(lambda);

    # And embed it into P*.
    mu2 := incl2[i];
    e_i_op := MinimalGeneratingSetOfModule(Source(mu2))[1];
    result := result + ImageElm(mu2, e_i_op ^ lambda_op);
  od;

  return result;
end;

##############################################################
#
# The same isomorphism as in FromHomToProjRep(), but in
# the opposite direction. We start with an element p
# of mP_star and we would like to get a morphism of
# representations f: mP --> mA
#
# Remark: the use of IsomorphicModules() is probably not very
# efficient and also the matrix could be computed more
# carefully.
#
##############################################################

FromProjRepToHom := function(p, mP, mP_star, mA, 1_mA)
  local proj, proj2, i, j, k, Ae_i, e_iA, proj_p, coeffs,
    as_algebra_element, PP, PP_op, A, A_op, lambda,
    lambda_op, v, proj2_v, matrix, as_algebra_element2,
    lambda2, result, K, image, matrices;

  A    := RightActingAlgebra(mP);
  A_op := RightActingAlgebra(mP_star);
  K    := LeftActingDomain(A);

  # Modules e_iA resp. Ae_i.
  PP    := IndecProjectiveModules(A);
  PP_op := IndecProjectiveModules(A_op);

  # Projections P*->Ae_i resp. P->e_iA
  proj  := DirectSumProjections(mP_star);
  proj2 := DirectSumProjections(mP);

  as_algebra_element := ProjectiveBasisVectorGens(PP_op);
  as_algebra_element2 := ProjectiveBasisVectorGens(PP);

  result := [];

  # For all projections Ae_i->P*.
  for j in [1..Length(proj)] do
    Ae_i := Range(proj[j]);

    # We figure out to which Ae_i we project.
    for i in [1..Length(PP_op)] do
      if (IsomorphicModules(PP_op[i], Ae_i)) then
        break;
      fi;
    od;

    # We project p to Ae_i, and we compute the corresponding element
    # of algebra A_op and also the opposite element of A.
    proj_p := ImageElm(proj[j], p);
    coeffs := Coefficients(Basis(Ae_i), proj_p);
    lambda := coeffs * as_algebra_element[i];
    lambda_op := OppositePathAlgebraElement(lambda);

    # We build the corresponding matrix of the map P->A.
    matrix := [];
    for v in BasisVectors(Basis(mP)) do
      e_iA := Range(proj2[j]);

      # We project v to e_iA.
      proj2_v := ImageElm(proj2[j], v);

      # We compute the corresponding element of the algebra A.
      coeffs := Coefficients(Basis(e_iA), proj2_v);
      lambda2 := coeffs * as_algebra_element2[i];
      image := (1_mA ^ lambda_op) ^ lambda2;

      Add(matrix, Coefficients(Basis(mA), image));
    od;

    result := result + matrix;
  od;

  matrices := ExtractHomMatrices(result, mP, mA);

  return RightModuleHomOverAlgebra(mP, mA, matrices * One(K));
end;

##############################################################
#
# Given a projective presentation s: mP1 --> mP0 of a module,
# and the duals mP0_star, mP1_star as representations of A^op,
# this function computes s^*: mP0_star --> mP1_star.
#
##############################################################

S_Star := function(s, mP0, mP1, mP0_star, mP1_star, mA, 1_mA)
  local v, f, fs, image, matrix, matrices, A, K;

  A := RightActingAlgebra(mP1);
  K := LeftActingDomain(A);

  matrix := [];
  for v in BasisVectors(Basis(mP0_star)) do
    f  := FromProjRepToHom(v, mP0, mP0_star, mA, 1_mA);
    fs := s * f;
    image := FromHomToProjRep(fs, mP1_star);
    Add(matrix, Coefficients(Basis(mP1_star), image));
  od;

  matrices := ExtractHomMatrices(matrix, mP0_star, mP1_star);

  return RightModuleHomOverAlgebra(mP0_star, mP1_star, matrices * One(K));
end;

##############################################################
#
# An auxiliary morphism in the spirit of Lian's thesis:
# it fixes an isomorphism between A^n and
# DirectSumOfModules(mP, mP_star)
# (see the SuppProjModule function above)
#
##############################################################

IsomorphismProjAndAn := function(mP1_P2, mAn)
  local iso, used, i, j,
        proj_P1_P2, proj_P1_P2_fin, proj_PX,
        incl_An, incl_An_fin, incl_A,
        f, g;

  # Projections P1_P2 ->> P1 resp. P1_P2 ->> P2 ...
  proj_P1_P2 := DirectSumProjections(mP1_P2);

  # ... composed with the projections P1 ->> e_iA resp. P2 ->> e_iA.
  proj_P1_P2_fin := [];
  for f in proj_P1_P2 do
    proj_PX := DirectSumProjections( Range(f) );

    for g in proj_PX do
      Add(proj_P1_P2_fin, f * g);
    od;
  od;

  # Inclusions A -> A^n ...
  incl_An := DirectSumInclusions(mAn);

  # ... composed with the inclusions e_iA ->> A.
  incl_An_fin := [];
  for f in incl_An do
    incl_A := DirectSumInclusions( Source(f) );

    for g in incl_A do
      Add(incl_An_fin, g * f);
    od;
  od;

  # Now we match the computed projections and inclusions
  # and add up the resulting maps P1_P2 -> A^n.
  iso := ZeroMapping(mP1_P2, mAn);
  used := [1..Length(incl_An_fin)];
  for g in proj_P1_P2_fin do
    for i in [1..Length(incl_An_fin)] do
      f := incl_An_fin[i];

      if (not used[i] = true) and Source(f) = Range(g) then
        iso := iso + g * f;
        used[i] := true;
        break;
      fi;
    od;
  od;

  return iso;
end;

##############################################################
#
# Another auxiliary morphism in the spirit of Lian's thesis:
# the opposite isomorphism to the one returned by
# IsomorphismProjAndAn() above.
#
##############################################################

IsomorphismAnAndProj := function(mP1_P2, mAn)
  local iso, used, i, j,
        incl_P1_P2, incl_P1_P2_fin, incl_PX,
        proj_An, proj_An_fin, proj_A,
        f, g;

  # Inclusions P1_P2 ->> P1 resp. P1_P2 ->> P2 ...
  incl_P1_P2 := DirectSumInclusions(mP1_P2);

  # ... composed with the inclusions P1 ->> e_iA resp. P2 ->> e_iA.
  incl_P1_P2_fin := [];
  for f in incl_P1_P2 do
    incl_PX := DirectSumInclusions( Source(f) );

    for g in incl_PX do
      Add(incl_P1_P2_fin, g * f);
    od;
  od;

  # Projections A -> A^n ...
  proj_An := DirectSumProjections(mAn);

  # ... composed with the projections e_iA ->> A.
  proj_An_fin := [];
  for f in proj_An do
    proj_A := DirectSumProjections( Range(f) );

    for g in proj_A do
      Add(proj_An_fin, f * g);
    od;
  od;

  # Now we match the computed projections and inclusions
  # and add up the resulting maps A^n -> P1_P2.
  iso := ZeroMapping(mAn, mP1_P2);
  used := [1..Length(proj_An_fin)];
  for g in incl_P1_P2_fin do
    for i in [1..Length(proj_An_fin)] do
      f := proj_An_fin[i];

      if (not used[i] = true) and Range(f) = Source(g) then
        iso := iso + f * g;
        used[i] := true;
        break;
      fi;
    od;
  od;

  return iso;
end;

##############################################################
#
# This function send m \in mM and n \in mN to the elementary
# tensor m \otimes_A n. Thus, it realizes the structure map
# of the tensor product over A, where the tensor product
# is represented as DHom_A(N,DM).
#
# Remark: The space Hom_A(N,DM) obtained as output of
# HomOverAlgebra() as well as the dual representation DM are
# supplied as the last two arguments so that
# one does not need to compute them again each time. Probably
# one would better define a new object for the tensor product,
# where the precomputed structure map (in some form) would be
# stored as an attribute.
#
# The function does assume that Basis(mDM) is the dual basis
# to Basis(mM) with respect to the canonical dot product!
#
##############################################################

 TensorProductMap := function(m, n, mM, mN, mDM, B_hom_mN_mDM)
  local coeffs_m, coeffs_f_i_n, i, B_hom_images, f_i_n;

  coeffs_m := Coefficients(Basis(mM), m);
  B_hom_images := [];

  f_i_n := List(B_hom_mN_mDM, f_i -> ImageElm(f_i, n));

  for i in [1..Length(f_i_n)] do
    coeffs_f_i_n := Coefficients(Basis(mDM), f_i_n[i]);

    B_hom_images[i] := coeffs_m * coeffs_f_i_n;
  od;

  return B_hom_images;
end;

##############################################################
# Almost split sequence algorithm ############################
##############################################################

AlmostSplitSequence2 := function(mX)
  local i, j, m, n,

        A, Q, K,

        # Variables to keep parts of a fixed projective presentation of mX
        t, mP0, mOmega, omega, kernel_inc, s, mP1,
        PP, PP_op, A_op, mA,

        # Auxiliary variables for the complement of P_1 in A^n (after Lian)
        supp, mP1s, mP1_mP1s, mAn,

        # Variables to keep information about the transpose
        mP0_star, mP1_star, multiplicities0, multiplicities1,
        s_star, t_hat, mTrX, mDTrX, B_hom_mDTrX_mOmega, 1_mA,

        # Variables for the key isomorphism
        # Hom_(P_1, \Omega) --> Hom_A(P_1, A) \times_A \Omega
        # (the notation should correspond to Lian's thesis)
        incl, e_iA, e_i, mu, psi, rho, nu, psi_inv, pi,

        # Variables for keeping the image of the the projective
        # cover P_1 \to \Omega under the latter isomorphism and the image
        # in Tr(X) \otimes_A \Omega
        mu_psi_rho, omega_pi_psi_inv_nu, omega_pi_psi_inv_nu_1_A,
        mu_psi_rho_el, psi_omega, t_mu_psi_rho_el,

        # Computing a nice basis for Tr(X) \otimes_A \Omega
        # (this will be affected by Lian's omission)
        mTrX_mOmega, B_mTrX_mOmega, B_mOmega, B_mTrX, n_images, m_n, V, B_V,
        B_V_new, added,

        # Translating the latter to a homomorphism \Omega \to DTt(X)
        # which represents an almost split sequence
        images, matrices, d_mOmega, d_mDTrX, used_x, used_y, dx, dy, xi,

        # And finally: the variables for constructing the almost split sequence
        mE, generator;

  A := RightActingAlgebra(mX);
  Q := QuiverOfPathAlgebra(A);
  K := LeftActingDomain(A);

  # A projective presentation for mX ##########################################

  t          := ProjectiveCover(mX);
  mP0        := Source(t);
  mOmega     := Kernel(t);
  omega      := ProjectiveCover(mOmega);
  kernel_inc := KernelInclusion(t);
  s          := omega * kernel_inc;
  mP1        := Source(omega);

  A_op  := OppositePathAlgebra(A);
  PP    := IndecProjectiveModules(A);
  PP_op := IndecProjectiveModules(A_op);

  mA    := DirectSumOfModules(PP);

  # A complement of P_1 inside A^n ############################################

  supp := SuppProjModule(mP1);
  mP1s := supp[2];
  n    := supp[1];
  mP1_mP1s := DirectSumOfModules([mP1, mP1s]);
  mAn := DirectSumOfModules( List([1..n], i -> mA) );

  # The transpose of mX with a proj. presentation #############################

  multiplicities0 := SuppProjModule(mP0)[3];
  mP0_star := [];
  for i in [1..Length(multiplicities0)] do
    for j in [1..multiplicities0[i]] do
      Add(mP0_star, PP_op[i]);
    od;
  od;
  mP0_star := DirectSumOfModules(mP0_star);

  multiplicities1 := SuppProjModule(mP1)[3];
  mP1_star := [];
  for i in [1..Length(multiplicities1)] do
    for j in [1..multiplicities1[i]] do
      Add(mP1_star, PP_op[i]);
    od;
  od;
  mP1_star := DirectSumOfModules(mP1_star);

  # We compute a generator of mA (the algebra as a representation) which
  # corresponds to 1_A (under a fixed isomorphism mA --> A_A)
  1_mA := Zero(mA);
  incl := DirectSumInclusions(mA);
  for i in [1..Length(incl)] do
    e_iA := Source(incl[i]);
    e_i := MinimalGeneratingSetOfModule(e_iA)[1];
    1_mA := 1_mA + ImageElm(incl[i], e_i);
  od;

  s_star := S_Star(s, mP0, mP1, mP0_star, mP1_star, mA, 1_mA);
  t_hat := CoKernelProjection(s_star);
  mTrX   := Range(t_hat);
  mDTrX := DualOfModule(mTrX);
  B_hom_mDTrX_mOmega := HomOverAlgebra(mOmega, mDTrX);

  # Preparation for the isomorphism ###########################################
  # Hom_(P_1, \Omega) --> Hom_A(P_1, A) \times_A \Omega #######################

  # Left hand side of the tensor product
  mu     := DirectSumInclusions(mP1_mP1s)[1];
  psi    := IsomorphismProjAndAn(mP1_mP1s, mAn);
  rho    := DirectSumProjections(mAn);

  # Right hand side of the tensor product
  nu     := DirectSumInclusions(mAn);
  psi_inv:= IsomorphismAnAndProj(mP1_mP1s, mAn); # ~ InverseOfIsomorphism (psi);
  pi     := DirectSumProjections(mP1_mP1s)[1];

  # Transferring \omega: P_1 \to \Omega to an element of Tr(X) \otimes \Omega #
  # (following Lian's thesis very closely) ####################################

  mu_psi_rho := mu * psi * rho;
  omega_pi_psi_inv_nu := nu * psi_inv * pi * omega;

  # omega * pi * psi^(-1) * nu(1_A).
  omega_pi_psi_inv_nu_1_A := List(omega_pi_psi_inv_nu, f -> ImageElm(f, 1_mA));

  # We compute the maps mu_psi_rho as elements of P_1^*.
  mu_psi_rho_el := List(mu_psi_rho, f -> FromHomToProjRep(f, mP1_star));
  t_mu_psi_rho_el := List(mu_psi_rho_el, el -> ImageElm(t_hat, el));

  # We compute the main basis element of Tr(X) \otimes \Omega.
  psi_omega := [];
  for i in [1..Length(t_mu_psi_rho_el)] do
    m := t_mu_psi_rho_el[i];
    n := omega_pi_psi_inv_nu_1_A[i];

    Add(psi_omega, TensorProductMap(m, n, mTrX, mOmega, mDTrX, B_hom_mDTrX_mOmega));
  od;
  psi_omega := Sum(psi_omega);

  # Completing the basis of Tr(X) \otimes \Omega ##############################
  # !!! This is the problematic part, among others affected by Lian's error ###

  mTrX_mOmega := [];

  B_mTrX_mOmega := [];

  B_mOmega := BasisVectors(Basis(mOmega));
  B_mTrX := BasisVectors(Basis(mTrX));
  for n in B_mOmega do
    n_images := [];

    for m in B_mTrX do
      m_n := TensorProductMap(m, n, mTrX, mOmega, mDTrX, B_hom_mDTrX_mOmega);

      Add(n_images, m_n);
      if not Sum(m_n) = 0 and not Sum(m_n) = Zero(K) then
        Add(B_mTrX_mOmega, m_n);
      fi;
    od;

    Add(mTrX_mOmega, n_images);
  od;

  V := VectorSpace(K, B_mTrX_mOmega);
  B_V := CanonicalBasis(V);
  B_V_new := [psi_omega];
  added := false;
  for i in [1..Length(B_V)] do
    if not psi_omega[i] = Zero(K) and not added then
      added := true;
    else
      Add(B_V_new, B_V[i]);
    fi;
  od;

 # Given a good basis B_hom_mDTrX_mOmega of Tr(X) \otimes \Omega, #############
 # this computes the induced map \Omega \to DTr(X) ############################

  # images[i][j] = 1st koeficient t_j\otimes\omega_i with respect to the basis B_mDTrX_Omega.
  images := [];
  for i in [1..Length(B_mOmega)] do
    Add(images, List(mTrX_mOmega[i], v -> Coefficients(Basis(V, B_V_new), v)[1] ));
  od;

  matrices := ExtractHomMatrices(images, mOmega, mDTrX);
  xi := RightModuleHomOverAlgebra(mOmega, mDTrX, matrices * One(K));

  # And the almost split seqeuence is just a pushout ##########################

  mE := PushOut(kernel_inc, xi);

  generator := [mE[1], CoKernelProjection(mE[1])];

  return generator;
end;







