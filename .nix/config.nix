{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  attribute = "ElmExtraction";

  default-bundle = "8.17";

  bundles."8.17" = {
    coqPackages.coq.override.version = "8.17";
    coqPackages.metacoq.override.version = "1.3.1-8.17";
  };
  bundles."8.18" = {
    coqPackages.coq.override.version = "8.18";
    coqPackages.metacoq.override.version = "1.3.1-8.18";
  };
  bundles."8.19" = {
    coqPackages.coq.override.version = "8.19";
    coqPackages.metacoq.override.version = "1.3.3-8.19";
  };
  bundles."8.20" = {
    coqPackages.coq.override.version = "8.20";
    coqPackages.metacoq.override.version = "1.3.4-8.20";
  };
  bundles."9.0" = {
    coqPackages.coq.override.version = "9.0";
    coqPackages.metacoq.override.version = "1.3.4-9.0";
  };

  ## Cachix caches to use in CI
  cachix.coq = {};
  cachix.coq-community = {};
  cachix.metacoq = {};

  cachix.au-cobra.authToken = "CACHIX_AUTH_TOKEN";
}
